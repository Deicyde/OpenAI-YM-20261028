import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Readout

set_option warningAsError false

/-!
# Re-frame and price a complete E variation

Coordinates crossing the absolute sum, simultaneous summed bills through
thousands or even infinitely many raw terms in all-field space. Extract
with explicit per-index choices and NO merging regular germs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Primary
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Finset
open Multi.Couples Pair
open Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} (C : Family G) {m p d N : ℕ} (o : SiteSpace C m p) {r κ b : ℝ}
    (Z : Config G (C.side m p)→ℂ)

/-- Keep raw& canonical dictionaries adjacent. Series paid NOT only at finitely
many rays. Declaration does not require output x `RealForm` or Orientation if input
symmetry supplied externally (can read from uniqueness per index). -/
structure Folio (d : ℕ) (r b : ℝ) where
  u : ℂ
  feeU : ‖u‖ ≤ b
  zone : ℕ → Support (C.side m p)
  func : ℕ → Config G (C.side m p)→ℂ
  fee : ℕ → ℝ
  v : ℕ → C.label d
  anchored i : o∈zone i
  pay i : 0 ≤ fee i
  finiteFee : SumBudget (fun i => burn (C.path.levels.budget m) (r+2) (zone i) * fee i) b
  literal : ∀ U,Z U = u + ∑' i,masked (C.path.levels.budget m).threshold (zone i) (func i) U
  charge i : (C.labels.level d).coeffSize (v i) ≤ patron C d * fee i
  path i : let P := C.path.levels.budget m
    let B := artifact C o (func i) (v i); let D := gap C o (zone i) (func i) (v i)
    Reads C.params o (zone i) ((C.labels.level d).coords.symm ((C.labels.level d).scaled P.threshold⁻¹ (v i))) (func i) ∧
      P.Regular (unionMap C o d (zone i)) B ∧ B 1=0 ∧
      (Nonwrapping (unionMap C o d (zone i)) o → C.params.PiVanish d o B) ∧
      P.supBounds o (unionMap C o d (zone i)) B (wage C d m * fee i) ∧
      Weight P (unionMap C o d (zone i)) D ∧ ∀ U, ‖D U‖ ≤ 4*wage C d m*fee i
  regularFee i U : ‖masked (C.path.levels.budget m).threshold (zone i) (func i) U‖ ≤ fee i

variable {C o Z}
lemma book (h : C.Makes) (hr : C.ref d ≤ m) {F : Config G (C.side m p)→ℂ} {o : SiteSpace C m p}
    (hE : ∃ (i : ℂ), ∃ E, (F=fun U => i+E U) ∧ ‖i‖≤b ∧ Banked (C.path.levels.budget m) (r+2) {o} E b) :
    Nonempty (Folio C o F d r b) := by
  let P := C.path.levels.budget m
  obtain ⟨u,E,rfl,hu,A,f,x,hx,hA,hf⟩ := hE
  have he (i) : P.Regular (A i) (f i) ∧ P.supBounds o (A i) (f i) (x i) := ⟨(hx i).2.1,(hx i).2.2.2 o (mem_singleton_self _)⟩
  choose v hw hv using fun i => piece C h hr o (A i) (he i).1 (he i).2
  exact ⟨⟨u,hu,A,f,x,v,fun i => (hx i).1 (mem_singleton_self _),fun i => (hx i).2.2.1,hA,
    fun i => congr_arg _ (hf i),hw,hv,fun i => price_through _ _ _ o (x i) (he i).2⟩⟩

-- bills & sums
variable (Y : Folio C o Z d r b)
lemma crossing {I : Type*} [NormedAddCommGroup I] [NormedSpace ℂ I] {d : ℕ}
    (f : C.label d → I) (hf : IsLinearMap ℂ f) (v : ℕ → C.label d) (hv : Summable v) :
    Summable (fun j => f (v j)) ∧ f (∑' j,v j)=∑' j,f (v j) := by
  let L := LinearMap.toContinuousLinearMap (hf.mk' f)
  exact ⟨(hv.hasSum.map L L.continuous).summable,L.map_tsum hv⟩

/-- For placing x after the readout. Exact linear operations even at
U in a LARGE-FIELD sector (no equality issues). -/
def canopy (C : Family G) {m p} (o : SiteSpace C m p) (v : C.label d) := masked
    (C.path.levels.budget m).threshold ((C.localSection d).footprint o) (marked C o v)
lemma canopy_linear {o : SiteSpace C m p} (U : Config G (C.side m p)) :
    IsLinearMap ℂ (fun v : C.label d => canopy C o v U) := by
  let T := C.labels.level d
  let V := C.localSection d
  have he := V.eval_linear
  unfold canopy marked exhibit
  by_cases hh : Healthy (C.path.levels.budget m).threshold ((C.localSection d).footprint o) U
  · simp_rw [masked_eq _ _ _ _ hh, SectionData.places]
    constructor
    · intro x y; rw [map_add,map_add,he.map_add]; rfl
    intro i x; rw [map_smul,map_smul,he.map_smul]; rfl
  simp_rw [masked_ne _ _ _ _ hh]; exact ⟨fun _ _ => (zero_add 0).symm,fun i _ => (smul_zero i).symm⟩
lemma canopy_unit (o : SiteSpace C m p) : canopy C o (C.labels.level d).e0=0 := by
  let F := C.labels.level d; let X := C.localSection d
  unfold canopy marked exhibit
  rw [show (C.labels.level d).core F.e0=0 by ext1 a; by_cases H:a=0 <;> simp [F,Frame.core,Frame.e0,H],map_zero]
  ext1 i; change masked _ _ _ _=0
  by_cases hh : Healthy (C.path.levels.budget m).threshold (X.footprint o) i
  · rw [masked_eq _ _ _ _ hh,SectionData.places,show (C.localSection d).evaluate 0=0 from map_zero (X.eval_linear.mk' _)]; rfl
  exact masked_ne _ _ _ _ hh

lemma fees (hr : 0 ≤ r) : SumBudget Y.fee b := permit_le Y.finiteFee le_rfl
    fun i => ⟨Y.pay i,le_mul_of_one_le_left (Y.pay _) (burn_ge _ (by linarith) _)⟩
lemma dimensions (hr : 0 ≤ r) : SumBudget (fun i => (C.labels.level d).coeffSize (Y.v i)) (patron C d*b) := by
  refine permit_le (permit_mul (fees Y hr) (zero_le_one.trans (patron_support C d))) le_rfl ?_
  exact fun j => ⟨Work.G08.size_nonneg ..,Y.charge j⟩
lemma voices_bank (hr : 0 ≤ r) : Summable Y.v :=
  Summable.of_norm_bounded ((dimensions Y hr).2.1) fun _i => Push.RelayDifference.norm_cost _ _
lemma each_price (hr : 0 ≤ r) :
    (C.labels.level d).coeffSize (Y.u • (C.labels.level d).e0 + ∑' i, Y.v i) ≤ (1+patron C d)*b := by
  let T := C.labels.level d
  let v := Y.v
  let z := Y.u
  have hc := dimensions Y hr
  have hw (i : T.Index) := crossing (fun x : C.label d => x i) ⟨fun _ _ => rfl,fun _ _ => rfl⟩ v (voices_bank Y hr)
  have he : (∑ i, ‖(∑' j,v j) i‖) ≤ patron C d*b := by
    let z (i : T.Index) j := ‖v j i‖
    have hg (i : T.Index) : Summable (z i) := hc.2.1.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => single_le_sum (f:=fun i => ‖v j i‖) (fun i _ => norm_nonneg _) (mem_univ i))
    calc
      _ = ∑ i, ‖∑' j,v j i‖ := sum_congr rfl fun i _ => congr_arg _ (hw _).2
      _ ≤ ∑ i,∑' j,z i j := Finset.sum_le_sum (fun j _ => norm_tsum_le_tsum_norm (hg j))
      _ ≤ _ := by rw [← Summable.tsum_finsetSum (f:=z) (fun i _ => hg i)]; exact hc.2.2
  calc
    _ ≤ ∑ i, (‖(z • T.e0) i‖ + ‖(∑' j,v j) i‖) := sum_le_sum fun i _ => norm_add_le ..
    _ ≤ _ := by
      have h : (∑ i, ‖(z • T.e0) i‖) = ‖z‖ := by
        rw [sum_eq_single (0:T.Index)]
        · simp [Frame.e0]
        · intro a _ he; simp [Frame.e0,he]
        simp
      rw [sum_add_distrib,h]; apply (add_le_add Y.feeU he).trans_eq; ring

/-- E reoriented including unit, actual placement/masks intact.
Return as BranchOne's `Coeff.x`; sums of D will pay separately. -/
def voice (Y : Folio C o Z d r b) := Y.u • (C.labels.level d).e0 + ∑' i, Y.v i

def patch (i) := unionMap C o d (Y.zone i)
def page (i) := artifact C o (Y.func i) (Y.v i)

def hole (i) := gap C o (Y.zone i) (Y.func i) (Y.v i)

-- summability retained for future applications
lemma takes (_hr : 0 ≤ r) (i) U : ‖masked (C.path.levels.budget m).threshold (patch Y i) (page Y i) U‖ ≤ wage C d m * Y.fee i :=
  price_through _ _ _ o _ ((Y.path i).2.2.2.2.1) U
lemma buckets (hr : 0 ≤ r) (U) : Summable (fun i => ‖hole Y i U‖) :=
  (((fees Y hr).2.1).mul_left (4*wage C d m)).of_nonneg_of_le (fun _ => norm_nonneg _) (fun i => (Y.path i).2.2.2.2.2.2 U)

lemma expression (hr : 0 ≤ r) (U) : Z U =
    (((voice Y) 0 + canopy C o (voice Y) U + ∑' i, masked (C.path.levels.budget m).threshold (patch Y i) (page Y i) U)) + ∑' i,hole Y i U := by
  have hp := voices_bank Y hr
  let m' := C.labels.level d
  let v := Y.v
  let c (i) := canopy C o (Y.v i) U
  let f i := v i 0
  let u i := hole Y i U
  let t i := masked (C.path.levels.budget m).threshold (patch Y i) (page Y i) U
  have ha (i) : masked (C.path.levels.budget m).threshold (Y.zone i) (Y.func i) U =
    ((t i + c i + f i)+u i) := by unfold t c u patch page hole gap f v canopy; dsimp only [Pi.sub_apply,Pi.add_apply]; abel
  let w (p : C.label d) := canopy C o p U
  have h := crossing (fun p : C.label d => p 0) ⟨fun _ _ => rfl,fun _ _ => rfl⟩ Y.v hp
  have hC := crossing w (canopy_linear _) Y.v hp
  have hu : Summable u := (buckets Y hr U).of_norm
  have ht : Summable t := Summable.of_norm_bounded ((fees Y hr).2.1.mul_left (wage C d m)) fun i => takes Y hr i U
  have hl : w (voice Y)=∑' i,c i := by
    have hw : IsLinearMap ℂ w := canopy_linear U
    unfold voice
    rw [hw.map_add,hw.map_smul,show w (C.labels.level d).e0=0 from congr_fun (canopy_unit o) U,smul_zero, zero_add]
    exact hC.2
  unfold w at hl
  rw [Y.literal,hl,show (voice Y) 0=Y.u+∑' i,f i from congr_arg₂ (· + ·) (by simp [Frame.e0]) h.2]
  simp_rw [ha]
  rw [Summable.tsum_add ((ht.add hC.1).add h.1) hu,Summable.tsum_add (ht.add hC.1) h.1,Summable.tsum_add ht hC.1]; abel

end YM.AnalyticNext.GridStop.Primary
