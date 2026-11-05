import YM.Extra.MULTISOURCE_TRAJECTORIES.BirthBounds
import YM.Extra.SOURCE_HISTORIES.Sizes
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Replay
import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Scale


/-!
# Exact finite input tensors of the weak-start calibration

Group ALL short regular C primaries, read the unmasked canonical (and
actual global unit), in E physical x units. We do NOT apply
an unmasked replacement to the density! Include all orders through the
chosen working Taylor degree t, with absolute costs and support criteria.
Not taking derivatives of a tsum of off-good functions (equating that
would need supplementary arguments). This is a finite symbol extraction,
not claiming yet any remainder/value approximation to the gauge density
at the new radius. K, masks, indicators and tails still belong to that
separate analysis.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Labels Source Source.Drops Cells Next.Extract Extraction
open Push.Corrected Push.Corrected.Issue Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {d m p N t l : ℕ}

/-- Use the OLD threshold at B.depth. -/
abbrev Screen (C : Family G) (m p t : ℕ) := Board G (C.side m p) (C.path.levels.budget m) t

def micro (C : Family G) (d m : ℕ) := (((C.S.a m : ℂ)^d)⁻¹)

def annal (C : Family G) (v : C.label d) (m N p i : ℕ) :=
    micro C d m • (chunk C v m N p).regular i

def paper (C : Family G) (d m N p i : ℕ) := (chunk C (0:C.label d) m N p).support i

def short (C : Family G) (d m N p i : ℕ) : Prop :=
    let W := C.path.levels.clock.coverSize m
    coverNumber W (paper C d m N p i) ≤ W

def printed (C : Family G) (v : C.label d) (m N p : ℕ) : Config G (C.side m p) → ℂ :=
    (C.localSection d).places ((C.labels.level d).scaled (θ C m)⁻¹ (primary C v m N p)) 0

-- origin cube for the calibration, NOT just canonical's immediate footprint.
structure Resolution (C : Family G) (d N : ℕ) (B : Screen C m p t) : Prop where
  orders : d ≤ t
  affordable : t ≤ (C.path.levels.budget m).order
  respects : C.ref d ≤ m
  covered : m ≤ N
  nonwrapping : Nonwrapping B.cube 0
  room : (C.localSection d).footprint (0:Site (C.side m p)) ⊆ B.cube
  news i : short C d m N p i → paper C d m N p i ⊆ B.cube

section Library
variable (h : C.Makes) (hr : C.ref d≤m) (hp : m≤N)
include h hr hp

-- Old combined unmasked canonical. Note footprints/flag logic stay separate.
omit hr in
theorem core_entry (v : C.label d) (U : Config G (C.side m p)) :
    let T := chunk C v m N p
    let P := T.x
    let F := C.labels.level d
    micro C d m * (P 0 + (C.localSection d).places (F.scaled (C.path.rep N p m).p.threshold⁻¹ (F.core P)) 0 U) =
      printed C v m N p U := by
  intro T P F
  let x := F.core P
  let e := (C.localSection d)
  rw [(h.wilson.represents N p m hp).vac]
  change micro C d m * (P 0 + e.evaluate (F.scaled (θ C m)⁻¹ x) (expandAt 0 U)) =
    e.evaluate (F.scaled _ (micro C d m • P)) _
  have he (q : ℝ) : F.scaled q P = F.scaled q x + P 0 • F.e0 := by
    nth_rw 1 [← Extra.Histories.Size.core_plus F P]
    rw [map_add,map_smul,F.scaled_unit]
  rw [map_smul, he,e.eval_linear.map_smul,e.eval_linear.map_add,e.eval_linear.map_smul,(h.sections d).unit]
  simp [add_comm]

lemma paper_eq (i p : ℕ) (v : C.label d) : paper C d m N p i = (chunk C v m N p).support i := by
  unfold chunk paper; simp only [chunk, ((h.calibrated d N p (hr.trans hp)).linear m hr hp).2.2.2]

def oil (C : Family G) (d m N p : ℕ) (v : C.label d) :=
    (C.path.levels.params m).columns * (C.labels.level d).coeffSize ((C.labels.level d).core (primary C v m N p))

/-- Spend the original remainder bills. -/
lemma annal_priced (p : ℕ) (v : C.label d) : ∃ c : ℕ → ℝ, Summable c ∧ ∑' i, c i ≤ oil C d m N p v ∧
    ∀ i, (C.path.levels.budget m).supBounds 0 (paper C d m N p i) (annal C v m N p i) (c i) := by
  let e := h.calibrated d N p (hr.trans hp)
  let R := (C.path.rep N p m)
  let u := micro C d m
  let F := C.labels.level d
  let L := (C.path.levels.params m).columns
  have ht := e.cap m hr hp ((C.factory d N p).terminal.symm v)
  obtain ⟨A,B,hA,hB,hT,-,⟨c,H,Y⟩,-⟩ := ht
  have he i := R.p.loMass ((chunk C v m N p).support i) (c i) (Y i).1
  have hb : Summable c := H.2.1.of_nonneg_of_le (fun i => (Y i).1) he
  refine ⟨fun i => ‖u‖*c i,hb.mul_left ‖u‖,?_,fun i => ?_⟩
  · have ha : ∑' i, c i ≤ A := (hb.tsum_le_tsum he H.2.1).trans H.2.2
    change A+B ≤ L * F.coeffSize (F.core (chunk C v m N p).x) at hT
    rw [tsum_mul_left]; apply (mul_le_mul_of_nonneg_left (ha.trans ((le_add_of_nonneg_right hB).trans hT)) (norm_nonneg _)).trans_eq
    unfold oil Issue.primary; rw [map_smul,Extra.Histories.Size.smul]; unfold u micro L F; ring
  rw [paper_eq h hr hp _ _ v, ← (h.wilson.represents N p m hp).vac]
  exact bound_smul u (Y i)

lemma annal_ok (p : ℕ) (v : C.label d) (i) :
    (C.path.levels.budget m).Regular (paper C d m N p i) (annal C v m N p i) := by
  rw [paper_eq h hr hp _ _ v,←(h.wilson.represents N p m hp).vac]
  exact regular_smul _ (((h.calibrated d N p (hr.trans hp)).format m hr hp _).smooth i)

omit hp in
lemma canon_ok (p : ℕ) (v : C.label d) :
    let Q := C.path.levels.budget m
    let x := primary C v m N p
    let f := printed C v m N p; let s := (C.localSection d).footprint (0:Site (C.side m p))
    Q.Regular s f ∧ Q.supBounds 0 s f ((C.path.levels.params m).columns * (C.labels.level d).coeffSize x) := by
  intro Q x f s; let F := C.labels.level d; let D := C.localSection d; let y := F.scaled Q.threshold⁻¹ x
  change Q.Regular s (D.places y 0) ∧ Q.supBounds _ _ (D.places y 0) _
  constructor
  · have hV (i : F.Index) := h.priced d m p hr 0 i
    rw [Extra.Trajectories.places_combined]
    exact (regular_bound_sum _ _ (fun i => ‖y i‖ *((C.path.levels.params m).columns * Q.threshold^(F.grades i).2)) (fun i _ =>
      ⟨regular_smul (y i) (hV i).1,bound_smul (y i) (hV i).2⟩)).1
  have he := Extra.Trajectories.places_priced h hr (0:Site (C.side m p)) y
  rw [(h.wilson.represents m p m le_rfl).vac] at he
  rw [show x=F.scaled Q.threshold y from (F.scaled_inv Q.threshold_pos.ne' x).symm]; exact he

lemma annal_linear (p : ℕ) (i : ℕ) : IsLinearMap ℂ fun v : C.label d => annal C v m N p i := by
  have H := ((h.calibrated d N p (hr.trans hp)).linear m hr hp).2.1
  constructor
  · intro a b; unfold annal chunk; rw [map_add, H.map_add]; rw [Pi.add_apply,smul_add]
  intro r a; unfold annal chunk; rw [map_smul,H.map_smul,Pi.smul_apply]; exact smul_comm ..

lemma canon_linear (p : ℕ) : IsLinearMap ℂ fun v : C.label d => printed C v m N p := by
  let F := (C.localSection d).eval_linear
  constructor
  · intro a b
    unfold printed; simp_rw [←primary_apply h hr hp,map_add]; funext U; rw [SectionData.places,F.map_add]; rfl
  intro r a; unfold printed; simp_rw [←primary_apply h hr hp,map_smul]; funext U; rw [SectionData.places,F.map_smul]; rfl
end Library

namespace Screen
open scoped Classical
variable (B : Screen C m p t)

def news (B : Screen C m p t) (v : C.label d) (N i : ℕ) (w : B.Word l) :=
    if short C d m N p i then B.print (annal C v m N p i) l w else 0

def notes (B : Screen C m p t) (v : C.label d) (N : ℕ) (w : B.Word l) :=
    B.print (printed C v m N p) l w + ∑' i, news B v N i w

variable (h : C.Makes) (hr : Resolution C d N B)
include h hr

lemma accounts (v : C.label d) (hl : l ≤ t) (w : B.Word l) :
    Summable (fun i => ‖news B v N i w‖) ∧ ∑' i, ‖news B v N i w‖ ≤ B.derivativeFee l * oil C d m N p v := by
  obtain ⟨c,hc,hC,Y⟩ := annal_priced h hr.respects hr.covered p v
  have hp := B.derivativeFee_nonnegative l
  have he i : ‖news B v N i w‖ ≤ B.derivativeFee l * c i := by
    unfold news; split_ifs
    · exact B.affordable (annal_ok h hr.respects hr.covered p v i) hr.affordable (Y i) l hl w
    rw [norm_zero]; exact mul_nonneg hp (Y i).1
  have ht := hc.mul_left (B.derivativeFee l)
  have H : Summable _ := ht.of_nonneg_of_le (fun i => norm_nonneg _) he
  refine ⟨H,(H.tsum_le_tsum he ht).trans ?_⟩
  rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hC hp

def ink (B : Screen C m p t) (d l : ℕ) := B.derivativeFee l * 2 * (C.path.levels.params m).columns *
    (Fintype.card (C.labels.level d).Index : ℝ)

omit h hr in
lemma ink_pos : 0 ≤ ink B d l := by
  unfold ink; have := B.derivativeFee_nonnegative l; have := (C.path.levels.params m).columns_ge; positivity

lemma writes (v : C.label d) (hl : l ≤ t) (w : B.Word l) :
    ‖notes B v N w‖ ≤ ink B d l * ‖primary C v m N p‖ := by
  obtain ⟨H,Y⟩ := canon_ok (N:=N) h hr.respects p v
  have hx := B.affordable H hr.affordable Y l hl w
  let u := primary C v m N p; let F := C.labels.level d
  let x := B.derivativeFee l; let r := (C.path.levels.params m).columns
  have hx' : 0 ≤ x := B.derivativeFee_nonnegative l
  have hr' : 0 ≤ r := zero_le_one.trans (C.path.levels.params m).columns_ge
  have hz : oil C d m N p v ≤ r*F.coeffSize u := mul_le_mul_of_nonneg_left (Work.G08.size_core F u) hr'
  have ht := accounts B h hr v hl w
  unfold notes; refine (norm_add_le ..).trans ((add_le_add hx ( (norm_tsum_le_tsum_norm ht.1).trans (ht.2.trans
    (mul_le_mul_of_nonneg_left hz hx')))).trans ?_)
  unfold ink; have he := mul_le_mul_of_nonneg_left (Extra.Histories.Size.le_norm F u) (mul_nonneg hx' hr')
  change x*(r*F.coeffSize u) + x*(r*F.coeffSize u) ≤ x*2*r*(Fintype.card F.Index:ℝ)*‖u‖
  linarith only [he]

omit h in
private lemma is_linear {X : Support (C.side m p)} (A : C.label d → Config G (C.side m p) → ℂ)
    (H : IsLinearMap ℂ A) (Y : ∀ x, (C.path.levels.budget m).Regular X (A x)) (hl : l ≤ t) (w : B.Word l) :
    IsLinearMap ℂ fun v => B.print (A v) l w := by
  have he v : ContDiffAt ℝ l (A v ∘ B.showAt) 0 := B.smooth (Y v) hr.affordable hl
  constructor
  · intro a b; unfold Board.print
    rw [H.map_add, show (A a+A b) ∘ _ = (A a ∘ B.showAt)+(A b ∘ B.showAt) from rfl,Tensor.coeff_add (he a) (he b)]
    rfl
  intro r a; unfold Board.print Tensor.coeff
  rw [H.map_smul, show (r • A a) ∘ _ = r • (A a ∘ B.showAt) from rfl, iteratedFDeriv_const_smul_apply (f:=A a ∘ B.showAt), smul_comm]; rfl
  exact he a

def record (hl : l ≤ t) (w : B.Word l) : C.label d →L[ℂ] ℂ := by
  have hc : IsLinearMap ℂ (fun v : C.label d => B.print (printed C v m N p) l w) :=
    is_linear B hr _ (canon_linear h hr.respects hr.covered p) (fun v => (canon_ok (N:=N) h hr.respects p v).1) hl w
  have he i : IsLinearMap ℂ (fun v : C.label d => news B v N i w) := by
    unfold news; split_ifs
    · exact is_linear B hr _ (annal_linear h hr.respects hr.covered p i) (fun v => annal_ok h hr.respects hr.covered p v i) hl w
    exact (0 : C.label d →ₗ[ℂ] ℂ).isLinear
  have ht v := ((accounts B h hr v hl w).1).of_norm
  refine LinearMap.toContinuousLinearMap ?_
  refine { toFun := fun v => notes B v N w, map_add' := ?_, map_smul' := ?_ }
  · intro a b; unfold notes; simp_rw [(he _).map_add,hc.map_add, (ht a).tsum_add (ht b)]; abel
  intro r a; unfold notes; simp_rw [(he _).map_smul, hc.map_smul, smul_eq_mul, tsum_mul_left]
  rw [mul_add]; rfl

end Screen
end YM.Further.CorrectedLift
