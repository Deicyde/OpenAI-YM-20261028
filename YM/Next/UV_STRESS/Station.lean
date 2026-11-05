import YM.Next.UV_STRESS.Vary
import YM.Org.Twist
import YM.Work.A05.Window


/-!
# UV comparison stations

Input boundary to the stress-grade argument. NO existence proof for these
physical estimates. They are at finite scale, on ordinary, not truncated,
Wilson moments. In particular they ask nothing about a choice of quotient
fields of S, angular interpolation, derivatives, or the maps even being of
full rank. Bounds do have to be simultaneous for the lift used. They include
separated compact joint tests through ties; order zero cost in the tests. This
kind of estimate could, for example, be sought via the strip and aligned array
regimes in E; it's not a consequence here of just the rank or of the existence
of S and a subsequence. Even though it's a bound on finite-scale measurements,
to be clear, it is a uniform bound (with epsilon slack in mesh-before-period
upper limit); **its production is a physical hypothesis**.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set MeasureTheory Analysis Extraction Table Ward Climb
open scoped Topology FourierTransform ContDiff BigOperators
variable {n : ℕ}

lemma point_dimension (n : ℕ) : Module.finrank ℝ (Points n)=4*n := by
  rw [(Points.flatten (n := n)).toLinearEquiv.finrank_eq,finrank_euclideanSpace]
  simp [mul_comm]

lemma enlarged {r : ℝ} (hr : 0 < r) (x : Points n) : x∈conf n ↔ r • x ∈ conf n := by
  refine ⟨Work.A05.smul_conf hr,fun h => ?_⟩
  have ht := Work.A05.smul_conf (inv_pos.mpr hr) h
  rwa [inv_smul_smul₀ hr.ne'] at ht

/-- Rescaling a flat joint test, including volume factor of 4n. -/
def dilate {r : ℝ} (hr : 0 < r) (t : Test n) : Test n := by
  let p := (↑((r^(4*n))⁻¹) : ℂ)
  let H (x : Points n) := t (r⁻¹ • x)
  have he : HasCompactSupport H := t.hasCompactSupport.comp_smul (inv_ne_zero hr.ne')
  refine ⟨fun x => p*H x, contDiff_const.mul (t.contDiff.comp (show ContDiff ℝ _ (fun x : Points n => r⁻¹ • x) by fun_prop)),
    he.mul_left,?_⟩
  let U := (fun x : Points n => r⁻¹ • x) ⁻¹' tsupport t
  have hU : IsClosed U := (isClosed_tsupport t).preimage (by fun_prop)
  apply subset_trans (b := U) (closure_minimal ?_ hU)
  · intro x hx; exact (enlarged (inv_pos.mpr hr) x).2 (show r⁻¹ • x ∈ conf n from t.tsupport_subset hx)
  intro x hx; apply subset_closure
  change t _ ≠ 0
  exact fun hy => hx (by change p*t _ = 0; rw [hy, mul_zero])

lemma zoom_integral (t : Test n) {r : ℝ} (hr : 0 < r) (K : Points n → ℂ) :
    (dilate hr t).applyTo K = t.applyTo fun x => K (r • x) := by
  let H (x : Points n) := t (r⁻¹ • x) * K x
  unfold Test.applyTo; change (∫ x, (↑((r^(4*n))⁻¹):ℂ)* t (r⁻¹ • x) * K x) = _
  simp_rw [mul_assoc]; rw [integral_const_mul]
  have hp := Measure.integral_comp_smul_of_nonneg volume H r (hR:=hr.le)
  rw [point_dimension, Complex.real_smul] at hp
  simpa [H, inv_smul_smul₀ hr.ne'] using hp.symm

variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Order}

abbrev Lifts (C : Family G) (D : ℕ) := (d : Fin (D+1)) → (Bel C.book).Field d →L[ℂ] C.book.Ref d

/-- Data for *one* station. Lift from free labels is not to S, these are
coefficients in the same Family used across all occurrences. -/
structure Station (C : Family G) (D : ℕ) where
  r : ℝ
  rad : 0 < r
  atCut : ℕ × ℕ → Lifts C D

variable {D : ℕ}
namespace Station
variable (X : Station C D)

/-- Actual normalized Wilson measurement. Fine-field literal positions in
`Order.smears`, repeated labels allowed. Family fixes all period/mesh/
reference scales. -/
def paid {n : ℕ} (v : Fin n → (Bel C.book).Tag) (h : ∀ i,(v i).1 ≤ D) (t : Test n) (N p : ℕ) : ℂ :=
    Order.smears C N p (fun i => ⟨(v i).1, X.atCut (N,p) ⟨(v i).1,Nat.lt_succ_of_le (h i)⟩ (v i).2⟩) (dilate X.rad t)

def charge {n : ℕ} (v : Fin n → (Bel C.book).Tag) := ∏ i, ‖(v i).2‖

/-- Upper bound for each actual cutoff test on the ordered tails, not limsup of
numbers with missing boundedness; eta slack implicit in `upper`. Uniform sup
cost, not simultaneous threshold over all smooth tests. `rank` here is the
ARITY cap. Complex labels, real-coordinate symmetry and real structure. -/
structure Admissible (F : Order) (H : (Bel C.book).RealSpin) (rank : ℕ) (R ε : ℝ) : Prop where
  lift_bound : ∃ A : ℝ, F.late fun N p => ‖X.atCut (N,p)‖ ≤ A
  lift_unit : F.late fun N p => X.atCut (N,p) (⟨0,Nat.succ_pos D⟩ : Fin (D+1)) ((Bel C.book).unit 0) = C.book.scalar 0
  lift_real : F.late fun N p => ∀ (i : Fin (D+1)) v, X.atCut (N,p) i ((Bel C.book).conj H i v) = star (X.atCut (N,p) i v)
  lift_signed : F.late fun N p => ∀ (i : Fin (D+1)) s v,
    X.atCut (N,p) i ((Bel C.book).mirror H i s v) = C.book.mirrorGroup i s (X.atCut (N,p) i v)
  short {n : ℕ} (hn : n ≤ rank) (v : Fin n → (Bel C.book).Tag) (hv : ∀ i, (v i).1 ≤ D)
    (t : Test n) (ht : tsupport t ⊆ Scaling.window R n) (M : ℝ) : 0<M → (∀ x, ‖t x‖ ≤ M) →
    F.upper (fun N p => ‖X.paid v hv t N p - t.applyTo (disc v)‖) (ε * charge v * M)

lemma refreshed {H k R ε} (ht : X.Admissible F H k R ε) (g : Order) : X.Admissible (F.refine g) H k R ε where
  lift_bound := ⟨_, Order.late_refine _ _ ht.lift_bound.choose_spec⟩
  lift_unit := Order.late_refine _ _ ht.lift_unit
  lift_real := Order.late_refine _ _ ht.lift_real
  lift_signed := Order.late_refine _ _ ht.lift_signed
  short n v hv t ht' M he h m hm := Order.late_refine F g (ht.short n v hv t ht' M he h m hm)
end Station

/-- Outstanding weak comparison receipts (besides the inputs to get the
Order & limits). Only arbitrary small good r for each size/tolerance. No
supposition about moving G/vacuum rep across uses. Not restricting to a
particular plateau formula; if using one to supply this it must be shown
to fit the same C and F. -/
structure Stations (C : Family G) (F : Order) (H : (Bel C.book).RealSpin) : Prop where
  arbitrarily (D N : ℕ) (R ε δ : ℝ) : 1 ≤ R → 0 < ε → 0 < δ →
    ∃ X : Station C D, X.Admissible F H N R ε ∧ X.r ≤ δ

variable {L : Register G}

abbrev Panel (S : Table L) := (d : ℕ) → (Bel L).Field d →ₗ[ℂ] S.Field d

def panels {S : Table L} (U : Panel S) (v : (Bel L).Tag) : S.Tag := ⟨v.1, U v.1 v.2⟩

def tested {n : ℕ} {S : Table L} (r : ℝ) (U : Panel S) (w : Fin n → (Bel L).Tag) (x : Points n) :=
    disc (panels U ∘ w) (r • x)

structure StraightAt (H : S.RealSpin) (h : (Bel C.book).RealSpin) (U : Panel S) (d : ℕ) : Prop where
  bars v : U d ((Bel C.book).conj h d v)=S.conj H d (U d v)
  reflects (s : Signed) v : U d ((Bel C.book).mirror h d s v)=S.mirror H d s (U d v)

/-- Read a station in the quotient S of `F.Ordered`. The temporary
subfilter is *only* to bound the same continuum kernels for every t (incl
tests with coordinate ties). No `N,p` diagonal used as a physical extraction. -/
lemma harvested (H : S.Hierarchy) (h : F.Ordered C S) (a : (Bel C.book).RealSpin)
    (X : Station C D) {N : ℕ} {R ε : ℝ} (hs : X.Admissible F a N R ε) :
    ∃ U : Panel S,
      (∀ d≤D, StraightAt H.spin a U d) ∧ U 0 ((Bel C.book).unit 0)=S.unit 0 ∧
      ∀ (n : ℕ), n ≤ N → ∀ v : Fin n → (Bel C.book).Tag, (∀ i,(v i).1 ≤ D) →
        ∀ t : Test n, tsupport t ⊆ Scaling.window R n →
        ∀ M : ℝ, 0 < M → (∀ x, ‖t x‖ ≤ M) →
        ‖t.applyTo (tested X.r U v) - t.applyTo (disc v)‖ ≤ ε * Station.charge v * M := by
  obtain ⟨A,hA⟩ := hs.lift_bound
  obtain ⟨b,hb,hU,Y,hY⟩ := finite_extract (𝓛:=F.fuse) X.atCut A hA
  have he i (x) : Tendsto (fun j => X.atCut j i x) b (𝓝 (Y i x)) :=
    Dash.arcing (tendsto_pi_nhds.mp hY i) tendsto_const_nhds
  let U (d : ℕ) : (Bel C.book).Field d →ₗ[ℂ] S.Field d :=
    if h : d≤D then (S.project d).comp (Y (⟨d,Nat.lt_succ_of_le h⟩ : Fin (D+1))).toLinearMap else 0
  have eq (d : ℕ) (h : d≤D) x : U d x=S.project d (Y ⟨d,Nat.lt_succ_of_le h⟩ x) := by simp only [U,dif_pos h]; rfl
  let z : Fin (D+1) := ⟨0,Nat.succ_pos _⟩
  refine ⟨U,fun d hd => ?_, ?_, fun n hn v hv t ht M hm ht' => ?_⟩
  · let i : Fin (D+1) := ⟨d,Nat.lt_succ_of_le hd⟩
    constructor
    · intro x; rw [eq d hd,eq d hd,S.conj_project]; apply congr_arg
      exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).conj a d x)) (he i x).star
        (((show ∀ᶠ j in F.fuse, ∀ (i : Fin (D+1)) v, X.atCut j i ((Bel C.book).conj a i v) = star (X.atCut j i v) from hs.lift_real)).filter_mono hb |>.mono fun _ h => h i x)
    intro s x; rw [eq d hd,eq d hd,S.mirror_project]; apply congr_arg
    exact tendsto_nhds_unique_of_eventuallyEq (he i ((Bel C.book).mirror a d s x))
      ((C.book.mirrorGroup d s).continuous_of_finiteDimensional.continuousAt.tendsto.comp (he i x))
      (((show ∀ᶠ j in F.fuse, ∀ (i : Fin (D+1)) s v, X.atCut j i ((Bel C.book).mirror a i s v) = C.book.mirrorGroup i s (X.atCut j i v) from hs.lift_signed)).filter_mono hb |>.mono fun _ h => h i s x)
  · rw [eq _ (Nat.zero_le _)]
    apply congr_arg (S.project 0)
    refine tendsto_nhds_unique_of_eventuallyEq (he z ((Bel C.book).unit 0)) tendsto_const_nhds ?_
    exact (show ∀ᶠ u in F.fuse, X.atCut u z ((Bel C.book).unit 0) = C.book.scalar 0 from hs.lift_unit).filter_mono hb
  let g : Caps n := fun i => (v i).1
  let m (j) (i : Fin n) : C.book.Ref (g i) := X.atCut j ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  let y (i : Fin n) : C.book.Ref (g i) := Y ⟨g i,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  have hh : S.integralOn g y (dilate X.rad t)=t.applyTo (tested X.r U v) := by
    unfold Table.integralOn; rw [zoom_integral]
    apply t.apply_eq; intro x hx
    change S.value g _ y = S.useAt S _ (panels U ∘ v)
    let l : Fin n → C.book.Token := fun i => ⟨g i,y i⟩
    rw [show panels U ∘ v = S.classTokens ∘ l from funext (fun i => by
      unfold panels Function.comp
      change Sigma.mk (g i) (U (g i) ((v i).2)) = Sigma.mk (g i) (S.project (g i) (y i))
      rw [eq _ (hv i)])]
    exact (S.at_project S H.laws.toSymmetric (fun _ => le_rfl) ((enlarged X.rad _).1 hx) l).symm
  have hz : Tendsto (fun j : ℕ×ℕ => X.paid v hv t j.1 j.2) b (𝓝 (t.applyTo (tested X.r U v))) := hh ▸
    calibrated_smear h b hb _ (v:=m) (x:=y) fun i => he ⟨(v i).1,Nat.lt_succ_of_le (hv i)⟩ (v i).2
  refine le_of_forall_pos_le_add fun η hη => ?_
  exact le_of_tendsto ((hz.sub_const (t.applyTo (disc v))).norm)
    ((show ∀ᶠ i in F.fuse, ‖X.paid v hv t i.1 i.2 - t.applyTo (disc v)‖ ≤ ε * Station.charge v * M + η from
      hs.short hn v hv t ht M hm ht' η hη).filter_mono hb)
end YM.Next.UVStress
