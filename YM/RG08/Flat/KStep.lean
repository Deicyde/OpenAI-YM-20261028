import YM.RG08.Flat.Pullback
import YM.Next.FREE_KERNELS.Rack
import YM.Next.STATIONARY.Loops.Fourier

/-!
# Cutoff sensitivity of the quadratic precision, one step

Two distinct diagonal Gaussian histories, at the same period and both
counting measure. Rather than a difference estimate for each pole formula,
use the cross identity with one `A0` from each history. The output proof is
on the cover strip, not read at that single period.
-/

set_option autoImplicit false
noncomputable section
namespace YM.RG08
open Function Filter Lattice Wilson RG Exterior Bloch Matrix Precision Next.Free
open Work.F08 Laurent
open scoped Topology BigOperators

variable {c f L : Side}

abbrev KRow := Row (TypeFace 1) (TypeFace 1)

/-- Ordinary potential Hessian, uncolored. -/
def hessian (B : Row (TypeFace 2) (TypeFace 2)) : KRow :=
    composeRows (composeRows (transRows (cobound 1)) B) (cobound 1)

lemma hessian_whole {B : Row (TypeFace 2) (TypeFace 2)} (h : Whole B) : Whole (hessian B) :=
    (((Whole.boundary 1).flipped).prod h).prod (Whole.boundary _)
lemma hessian_acts {B : Row (TypeFace 2) (TypeFace 2)} (h : Whole B) (c : Side) :
    (hessian B).acts c = K (B.acts c) := by
  rw [hessian, (((Whole.boundary _).flipped).prod h).acts (Whole.boundary _),
      ((Whole.boundary _).flipped).acts h, acts_trans]; rfl
lemma hessian_read {B : Row (TypeFace 2) (TypeFace 2)} (h : Whole B) {p : Momentum} (hp : physical p) :
    (hessian B).read p = Stationary.dcross B p := by
  unfold Stationary.dcross
  have hx : ((cobound 1).read p)ᴴ = (symbol 1 (-p))ᵀ := by
    rw [← Exterior.reading]; ext i j
    have hh := Row.conjugate (cobound 1) p
    rw [show star p=p from hp] at hh
    rw [conjTranspose_apply, Matrix.transpose_apply, hh]; rfl
  rw [hessian, (((Whole.boundary _).flipped).prod h).read (Whole.boundary _) hp,
      ((Whole.boundary _).flipped).read h hp, read_opposite _ hp,hx,Exterior.reading]

lemma hessian_price (η : ℝ) (he : 0 ≤ η) :
    ∃ c : ℝ, 0 < c ∧ ∀ B : Row (TypeFace 2) (TypeFace 2), ∀ A,
      B.strip η A → (hessian B).strip η (c*A) := by
  obtain ⟨X,hX,H⟩ := delta_budget 1 η
  have h : Nonempty (TypeFace 2) := ⟨plaquette ⟨(0,1),by decide⟩⟩
  let q := (Fintype.card (TypeFace 2):ℝ)
  refine ⟨q^2*X^2, by unfold q; positivity,fun B A ha => ?_⟩
  refine strip_mono (strip_compose he (strip_compose he (strip_trans H) ha) H) le_rfl ?_
  exact le_of_eq (by unfold q; ring)

lemma hessian_difference_zero {A B : Row (TypeFace 2) (TypeFace 2)} (ha : Whole A)
    (hb : Whole B) (h : A.read 0=B.read 0) :
    ZeroOrder 3 (minusRows (hessian A) (hessian B)) := by
  intro i j
  have hg p : physical (Stationary.axes p) := Stationary.axes_real p
  simp only [read_less (hessian_whole ha).safe (hessian_whole hb).safe (hg _),
    hessian_read ha (hg _),hessian_read hb (hg _),Matrix.sub_apply]
  apply Stationary.bed_gain (K:=1)
  intro p q
  obtain ⟨s,C,hs,H⟩ := ha
  obtain ⟨t,D,ht,G⟩ := hb
  have hz : AnalyticAt ℝ (fun k : Corn Axis => A.read (Stationary.axes k) p q -
      B.read (Stationary.axes k) p q) 0 :=
    ((Stationary.Firm.of_series (Row.constant_strip A H p q) hs).analytic_real (0:Corn Axis)).sub
      ((Stationary.Firm.of_series (Row.constant_strip B G p q) ht).analytic_real (0:Corn Axis))
  exact (Stationary.rays_at_zero hz).2 (by rw [Stationary.axes_origin,h,sub_self])

lemma k_symmetric {H : Matrix (Body 2 c) (Body 2 c) ℝ} (h : Hᵀ=H) :
    (K H)ᵀ=K H := by rw [K,transpose_mul,transpose_mul,h,transpose_transpose,Matrix.mul_assoc]

/-- Schur difference without changing block or scalar norm. Enough to have
    symmetry at the priming slot. -/
theorem cross_identity (S : StepData c f) {A A' : Matrix (Body 2 f) (Body 2 f) ℝ}
    {B B' : Matrix (Body 2 c) (Body 2 c) ℝ} {P Q : Matrix (Body 1 f) (Body 1 c) ℝ}
    (ha : Aᵀ=A) (hb : Bᵀ=B) (h : Inputs S P A B) (h' : Inputs S Q A' B') :
    K B-K B' = Pᵀ * (K A-K A') * Q := by
  have he : Pᵀ * K A= K B * mean S := by
    have hx := congr_arg Matrix.transpose h.primal
    rwa [transpose_mul, k_symmetric ha, transpose_mul,k_symmetric hb,transpose_transpose] at hx
  have hp : Pᵀ * K A * Q= K B - S.kernel.penalty⁻¹ • (K B * K B') := by
    rw [he, Matrix.mul_assoc,h'.dual, Matrix.mul_sub,Matrix.mul_one,Matrix.mul_smul]
  have hq : Pᵀ * K A' * Q= K B' - S.kernel.penalty⁻¹ • (K B * K B') := by
    rw [Matrix.mul_assoc, h'.primal,← Matrix.mul_assoc,← transpose_mul,h.dual,
      transpose_sub,transpose_smul,k_symmetric hb,transpose_one,Matrix.sub_mul,Matrix.one_mul,
      Matrix.smul_mul]
  rw [Matrix.mul_sub,Matrix.sub_mul,hp,hq]
  abel

/-- Kronecker records from a cofinal list of tori suffice to identify the
    pullback on the infinite cover. No positivity/gap assumptions on this
    linear identity; those are separate requirements in forming the Gaussian. -/
theorem cross_pullback (s n : ℕ→Side) (S : ∀ i, StepData (s i) (n i))
    (L : Side) (hl : ∀ i,(S i).patch.L=L)
    (hn : Tendsto (fun i => (s i).val) atTop atTop)
    {A B C D : Row (TypeFace 2) (TypeFace 2)}
    {P Q : Cross L (TypeFace 1) (TypeFace 1)}
    (ha : Whole A) (hb : Whole B) (hc : Whole C) (hd : Whole D)
    (hp : Whole P) (hq : Whole Q)
    (h : ∀ᶠ i in atTop, let f := n i; let c := s i
      let g : Ratio c f := ⟨L,(hl i ▸ (S i).sizes)⟩
      Inputs (S i) (installed g P) (A.acts f) (C.acts c) ∧
        Inputs (S i) (installed g Q) (B.acts f) (D.acts c) ∧
        (A.acts f)ᵀ=A.acts f ∧ (C.acts c)ᵀ=C.acts c) :
    minusRows (hessian C) (hessian D)=pullbackRows P Q (minusRows (hessian A) (hessian B)) := by
  refine row_ext_tail hn ((hessian_whole hc).minus (hessian_whole hd)).safe
    (pullback_whole hp hq ((hessian_whole ha).minus (hessian_whole hb))).safe ?_
  filter_upwards [h] with i hi
  let g : Ratio (s i) (n i) := ⟨L,(hl i ▸ (S i).sizes)⟩
  rw [(hessian_whole hc).less (hessian_whole hd), hessian_acts hc, hessian_acts hd,
      pullback_acts (w:=g) hp hq ((hessian_whole ha).minus (hessian_whole hb)),
      (hessian_whole ha).less (hessian_whole hb),hessian_acts ha,hessian_acts hb]
  exact cross_identity (S i) hi.2.2.1 hi.2.2.2 hi.1 hi.2.1

/-- Numerical gate to consume. Must choose widths on the previous/coarser
 step before imposing the length threshold; same interface at a transition. -/
def KContraction (L : Side) (σ τ C : ℝ) : Prop :=
    ∀ P Q : Cross L (TypeFace 1) (TypeFace 1), P.strip τ (C/L.val) →
      (∀ s : List Axis,s.length ≤ 3 →
        (advanceC L Q s).strip τ (C/(L.val:ℝ)^(1+s.length))) →
    ∀ D : KRow, ∀ A, 0 ≤ A → D.strip σ A → ZeroOrder 3 D →
      (pullbackRows P Q D).strip τ (A/Real.sqrt L.val)

/-- Hessian difference gate-uniform contract. Widths and derivative prices
    independent of the block length. Gives `L^(-1/2)` after block choice. -/
lemma large_contraction (σ τ C : ℝ) (hs : 0<σ) (ht : 0<τ) :
    ∃ N : ℕ, ∀ L : Side, N ≤ L.val → Odd L.val → KContraction L σ τ C := by
  obtain ⟨η,K,hη,-,hK,H⟩ := pullback_gain (TypeFace 1) (TypeFace 1) σ τ C hs ht 3
  obtain ⟨k,hk⟩ := exists_nat_gt (max (τ/η) (K^2))
  refine ⟨k,fun L hl ho p q h hp D A ha ha' he => ?_⟩
  have hL : max (τ/η) (K^2) ≤ L.val := hk.le.trans (by exact_mod_cast hl)
  have hb := (le_max_right ..).trans hL
  have hu := Real.sq_sqrt (x:=(L.val:ℝ)) (by positivity)
  have hD : 0 < Real.sqrt (L.val:ℝ) := by positivity
  have hm : K ≤ Real.sqrt L.val := (pow_le_pow_iff_left₀ hK hD.le (by decide : 2≠0)).1 (hu.symm ▸ hb)
  refine strip_mono (H L ho ((div_le_iff₀ hη).1 ((le_max_left ..).trans hL)) p q h hp D A ha ha' he) le_rfl ?_
  calc
    _ ≤ Real.sqrt L.val*A*(L.val:ℝ)^2/(L.val:ℝ)^3 := by gcongr
    _ = _ := by field_simp
                calc
                  _ = A*(Real.sqrt L.val)^2 := by ring
                  _ = _ := by rw [hu]

end YM.RG08
