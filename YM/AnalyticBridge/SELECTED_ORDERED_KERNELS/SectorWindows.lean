import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.SectorData
import YM.Next.BOUNDARY.Derived

/-!
# Use the window engine and then the inverse engine AGAIN on the same
# sector covariance. Windows are exactly SectorChange's endpoint scheme

No positivity by mere symmetrization; the fixed-L second gap is from
`ground_supply`. Lemmas here keep both gaps explicit for reuse. In particular
the second inverse may be on a *marginal* of C, not an inverse entry of the
first A on the same slot set. Freeze all geometry including at equality;
the correction identity needed here is on the open exponential chart germ
where the counting matrices remain invertible (largeness tested just at V).
Ordinary intermediate bills avoid repeated frame conversion. See SectorLie
for Lie conclusions on precisely these Config functions.
-/

set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Sector
open Lattice Wilson RG Function Filter WardBin.Lies Precision Tree Next.SectorChange
  YM.Pressure Rows Wisps FreeResolvent Affine Mark TestD Window
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x : ℝ}

section general
variable {ι X Y τ : Type*} [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℝ X]
  {v : τ → X} {C : Mark τ Y} {D : Cost Y} {a : ι → Y} {k : ℕ} {d s M δ s' : ℝ} {F H : X → Matrix ι ι ℝ} {t : X}

def polarize {X : Type*} (F : X → Matrix ι ι ℝ) : X → Matrix ι ι ℝ := fun x => (1/2:ℝ) • (F x+(F x).transpose)

omit [Fintype ι] [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma polarize_sub (h : ∀ x, Matrix.IsSymm (H x)) : polarize (F-H) = polarize F - H := by
  ext x i j; simp only [Pi.sub_apply, polarize,Matrix.transpose_sub,(h x).eq,Matrix.smul_apply,Matrix.add_apply,Matrix.sub_apply,smul_eq_mul]; ring

lemma polarize_cost (h : Bundle v C D a a F t k s M) : Bundle v C D a a (polarize F) t k s M :=
  ((h.one_add h.transpose).scale (1/2:ℝ)).mono le_rfl (by rw [abs_of_nonneg (by norm_num)]; linarith)

lemma amend {v : raw G c → X} {p : Edge (Site c) → Y}
    (h : Bundle v (positions D (p ∘ edge) d) D a a F t k s M) (hd : δ ≤ d) (hs : s' ≤ s) : Bundle v (positions D (p ∘ edge) δ) D a a F t k s' M := by
  refine ⟨h.smooth,fun l hl => ?_⟩
  have hb := (h.bound l hl).mono hs le_rfl
  nth_rw 1 [← List.ofFn_get l] at hb ⊢
  exact ⟨discount hb.row hd,discount hb.col hd⟩

variable [DecidableEq ι]
omit [NormedAddCommGroup X] [NormedSpace ℝ X] in
lemma invert_error (h : Neat H 0 t) (he : Neat F 0 t) : TestD.action H 0 t - F t =
    (-1:ℝ) • ((TestD.action H 0 t*(H t - TestD.action F 0 t))*F t) := by
  simp only [Neat,zero_smul,add_zero] at h he
  simp only [TestD.action,resolve,zero_smul,add_zero]
  rw [Matrix.mul_sub,Matrix.nonsing_inv_mul _ h,Matrix.sub_mul,Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ he,Matrix.one_mul,Matrix.mul_one]; simp
end general

variable {V : Config G c} {A : Stores S} {T : Forest S.ratio} {k : S.Choices} {H : Tube G S} {q : ℕ}
  {s M r d Y g δ Y' : ℝ}

abbrev chartBundle (A : Stores S) (T : Forest S.ratio) (V : Config G c) (q : ℕ) (d s M : ℝ)
    (F : Config G c → Matrix (In (G:=G) x A T) (In (G:=G) x A T) ℝ) :=
  Bundle (ray G c) (marks G c d) (native c) (front A T) (front A T) (over F V) 0 q s M

def openings (A : Stores S) (T : Forest S.ratio) (G : Gauge) (h : 120 ≤ radiusB x) := survey (boards A T G h)

def rough (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (h : 120 ≤ radiusB x) (u : ℝ) :=
  columns (openings A T G h) (form H x A T k) u

def exactInv (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) (u : ℝ) := resolver (form H x A T k) u

def marginal {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices)
    (e : ι → In (G:=G) x A T) (u : ℝ) := resolver (fun V => (covariance H x A T k V).submatrix e e) u

def kernel (H : Tube G S) (x : ℝ) (A : Stores S) (T : Forest S.ratio) (k : S.Choices) :=
  resolver (covariance H x A T k) 0 - form H x A T k


lemma pair_same (hb : 120 ≤ radiusB x) : covariance H x A T k = polarize (rough H x A T k hb 0) := by
  funext V; dsimp only [rough,columns,openings,covariance,fog,Schur.clouded,polarize]
  exact congr_arg (fun z : Matrix (In (G:=G) x A T) (In (G:=G) x A T) ℝ => (1/2:ℝ) • (z+z.transpose))
    ((inspect_arbitrary _ (form H x A T k V)).symm)
lemma pair_error (hb : 120 ≤ radiusB x) : covariance H x A T k - exactInv H x A T k 0 =
    polarize (rough H x A T k hb 0 - exactInv H x A T k 0) := by
  rw [pair_same hb,polarize_sub]; rw [exactInv,resolver_zero]; exact fun _ => form_sym.inv

def count (q : ℕ) (M Y r : ℝ) := meter q q M 1 (rise Y r)
lemma drain_zero : drain 0 = 1 := by simp [drain]

def savings (q : ℕ) (x d M Y r u : ℝ) := patchFee d (radiusB x/60 : ℕ) M 1 Y (count q M Y r * drain u) q

variable (p : Price s M r d 1 Y 1 q)
include p
lemma count_nn : 0 ≤ count q M Y r := p.meter_abs
lemma savings_nn {u : ℝ} (hu : 0 ≤ u) : 0 ≤ savings q x d M Y r u := patch_nonneg (mul_nonneg p.meter_abs (drain_pos hu).le) p

variable (hA : Data (native c) (front A T) Prod.fst q s M r d 1 (form H x A T k) V)
  (hy : (native c).Volume (front (G:=G) (x:=x) A T) d Y) (hR : 120 ≤ radiusB x)
include hA hy hR

lemma cloud_bill : chartBundle A T V q d (3*(q+1:ℕ)*d) (Y*count q M Y r) (covariance H x A T k) := by
  rw [pair_same hR]
  let Z := openings A T G hR
  apply polarize_cost (F:=over (rough H x A T k hR 0) V)
  constructor
  · exact glimpse_smooth hA Z le_rfl p.r0
  intro l hl
  refine (glimpse_rates hA p Z (u:=0) le_rfl (position_move _ _ p.pos.le) hy l hl).mono le_rfl ?_
  rw [drain_zero,charges]; split <;> simp [count]

lemma cloud_savings : chartBundle A T V q d d (savings q x d M Y r 0) (covariance H x A T k - exactInv H x A T k 0) := by
  rw [pair_error hR]
  exact polarize_cost (hA.discrepancy p (u:=0) le_rfl (position_move _ _ p.pos.le) hy (near_survey (boards A T G hR)))

variable (hC : FreeResolvent.Gap (covariance H x A T k V) g) (p' : Price d (Y*count q M Y r) g δ 1 Y' 1 q)
include hC p'

lemma cloud_data : Data (native c) (front A T) Prod.fst q d (Y*count q M Y r) g δ 1 (covariance H x A T k) V := by
  let F := over (covariance H x A T k) V
  have he : d ≤ 3*(q+1:ℕ)*d := by have := p.pos; push_cast; nlinarith [show 0 ≤ (q:ℝ)*d by positivity]
  have hb : Bundle (ray G c) (marks G c δ) (native c) (front A T) (front A T) F 0 q d (Y*count q M Y r) :=
    amend (p:=Prod.fst) (cloud_bill p hA hy hR) (room_le p') he
  have hz := hb.bound [] (by simp)
  rw [zeroth] at hz
  refine ⟨hb.smooth,?_ ,hz.reclaim,fun l _ hl => ?_⟩
  · simpa only [over,map_zero,Motion.increment_zero] using hC
  rw [mul_one]; exact hb.bound l hl

variable (hy' : (native c).Volume (front (G:=G) (x:=x) A T) δ Y')
include hy'

def haul (q : ℕ) (x d M Y Y' r g : ℝ) :=
  tagPrice 1 q (tagPrice 1 q (count q (Y*count q M Y r) Y' g) (savings q x d M Y r 0)) M

omit hA hy hR hC hy' in
lemma haul_nn : 0 ≤ haul q x d M Y Y' r g := tag_nn (tag_nn (count_nn p') (savings_nn p (u:=0) le_rfl)) p.m

/-- Small term, INCLUDING its ordered jet input bills before conversion;
price ∝ exp(-const*radiusB x) up to rounding with two post-L widths, also
at derivative order zero. No annulus or determinant expansion. -/
lemma residual : chartBundle A T V q δ δ (haul q x d M Y Y' r g) (kernel H x A T k) := by
  let C := over (covariance H x A T k) V; let Q := over (form H x A T k) V; let K := Y*count q M Y r
  let m := marks G c δ; let D := native c; let a := front A T (x:=x) (G:=G); let v := ray G c
  let u := count q K Y' g
  let F := TestD.action C 0; let E := C - TestD.action Q 0
  have hF := cloud_data p hA hy hR hC p'
  have hm := (position_move (native c) (hearth (G:=G) (r:=1)) p'.pos.le)
  have hf := hF.volume_price (u:=0) p' le_rfl hm hy'
  rw [drain_zero,mul_one] at hf
  change Bundle v m D a a F 0 q (4*(q+1:ℕ)*δ) u at hf
  let s' : ℝ := 4*(q+1:ℕ)*δ
  have hs' : s' ≤ d := p'.roomEnough.trans p'.roomTop
  let e := savings q x d M Y r 0
  have he : Bundle v m D a a E 0 q s' e := amend (p:=Prod.fst) (cloud_savings p hA hy hR) (room_le p') hs'
  have hQ : Bundle v m D a a Q 0 q s' M := amend (p:=Prod.fst) (hA.bundle p.m le_rfl) (room_le p') (hs'.trans (room_le p))
  let R : ℝ := (q+1:ℕ)*δ
  have hδ := p'.pos.le
  have h' : R+q*δ ≤ s' := by unfold R s'; push_cast; nlinarith [show (0:ℝ)≤q*δ by positivity]
  have hu : 0 ≤ u := count_nn p'; have hE : 0 ≤ e := savings_nn p (u:=0) le_rfl
  have hh := hf.multiply he hm hδ le_rfl hu hE (by unfold R; positivity) h'
  have hr : δ+q*δ ≤ R := by unfold R; push_cast; linarith
  have hP : Bundle v m D a a (fun x => (F x*E x)*Q x) 0 q δ (haul q x d M Y Y' r g) :=
    hh.multiply (hQ.mono ((le_add_of_nonneg_right (by positivity)).trans h') le_rfl) hm hδ le_rfl (tag_nn hu hE) p.m hδ hr
  apply ((hP.scale (-1)).mono le_rfl (le_of_eq (by rw [abs_neg,abs_one,one_mul]))).glue
  filter_upwards [germ_valid (hA.localUnit (u:=0) le_rfl p.r0) hA.smooth.continuousAt,
    germ_valid (hF.localUnit (u:=0) le_rfl p'.r0) hF.smooth.continuousAt] with z hQ hC
  exact (invert_error hC hQ).symm
end YM.SelectedOrderedKernels.Sector
