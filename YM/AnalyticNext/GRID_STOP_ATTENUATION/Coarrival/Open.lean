import YM.AnalyticNext.GRID_STOP_ATTENUATION.Alphabet.Mint
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Ballast
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Clerk
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Folio
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Weave
import YM.Push.RELAY_DIFFERENCE.Shuffles


set_option warningAsError false

/-! # Probe preparation at an internal calibration station

Thick cost: pay by true compulsory Pack budget at the ordinary exponent,
NOT by advocating a stronger given Based column for this station. Even at
this small demand need late thresholds and room. No correction to x allowed,
no propagation yet. -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Coarrival
open Function Filter MeasureTheory RG Marker Wilson Lattice Source Bid Labels Multi Stock Multi.Couples Finset
open Push.GridApprox
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {C : Family G} {m d p N : ℕ}
variable {n : Side}

/-- Caller's dictionary indexed i for regular entries. Supports stored separately
for alignment inherited via programs (including old factory requirements). -/
abbrev Wire (F : Frame G d) (n : Side) := F.Coeff × (ℕ → Config G n → ℂ) × (ℕ → Config G n → ℂ)
variable {F : Frame G d}

def address (X : ℕ → Support n) (D : Wire F n) : Coefficient F n := ⟨D.1,X,D.2.1,D.2.2⟩
def wire (D : Coefficient F n) : Wire F n := ⟨D.x,D.regular,D.forced⟩



variable (S : SectionData F) (o : Site n)

def kit (t : ℝ) (v : F.Coeff) : Vessel G n where
  siteSet := S.footprint o
  tall := v 0
  seen := S.places (F.scaled t⁻¹ (F.core v)) o

variable {P : Rep G n}

lemma complete_kit (h : S.Sound C.params) (t : ℝ) (v : F.Coeff) :
    (kit S o t v).full = S.places (F.scaled t⁻¹ v) o := by
  have hv : v= v 0 • F.e0+ F.core v := by ext1 i; by_cases e:i=0 <;> simp [Frame.e0,Frame.core,e]
  conv_rhs => rw [hv,map_add,map_smul,F.scaled_unit]
  unfold kit Vessel.full SectionData.places
  simp only
  funext U
  rw [S.eval_linear.map_add,S.eval_linear.map_smul,h.unit]; simp

lemma tail_is (v : F.Coeff) : (kit S o (P.p.threshold) v).tail P=
    S.places (F.scaled P.p.threshold⁻¹ (F.core v)) o - masked P.p.threshold (S.footprint o)
      (S.places (F.scaled P.p.threshold⁻¹ (F.core v)) o) := by
  funext u; unfold kit Vessel.tail Vessel.cheek Vessel.full; dsimp only [Pi.sub_apply]; abel

lemma kit_copies (v : F.Coeff) (h : S.Sound C.params) : Weight P.p (S.footprint o) ((kit S o (P.p.threshold) v).tail P) :=
  (kit S o P.p.threshold v).tail_weight _ (S.placed_local o _) (S.continuous_places ..).measurable (S.placed_invariant h o _)

def beginAt (h : Room P) (v : F.Coeff) : Wire F n := let t := P.p.threshold
    ⟨v,0,Primary.allocate h (ballast (S.footprint o) P ((kit S o t v).tail P))⟩

/-- Born as one common dictionary. -/
lemma begin_linear (h : Room P) : IsLinearMap ℂ (beginAt S o h) := by
  let t := P.p.threshold; let L := S.footprint o
  let f (v : F.Coeff) := (kit S o t v).tail P
  have he : IsLinearMap ℂ f := by
    have hv := S.eval_linear
    constructor
    · intro i j; funext U
      unfold f; rw [tail_is,tail_is,tail_is,map_add,map_add]; by_cases H: Healthy P.p.threshold (S.footprint o) U
      · simp only [Pi.sub_apply,masked_eq _ _ _ _ H,sub_self,Pi.add_apply,add_zero]
      simp only [Pi.sub_apply,masked_ne _ _ _ _ H,sub_zero,Pi.add_apply]; exact congr_fun (hv.map_add ..) _
    intro i j; funext U
    unfold f; rw [tail_is,tail_is,map_smul,map_smul]; by_cases H: Healthy P.p.threshold (S.footprint o) U
    · simp only [Pi.sub_apply,masked_eq _ _ _ _ H,sub_self,Pi.smul_apply,smul_zero]
    simp only [Pi.sub_apply,masked_ne _ _ _ _ H,sub_zero,Pi.smul_apply]; exact congr_fun (hv.map_smul ..) _
  constructor
  · intro x y
    refine Prod.ext rfl (Prod.ext (zero_add _).symm ?_)
    funext j U; change Primary.allocate h (ballast _ _ (f (x+y))) j U = Primary.allocate h (ballast _ _ (f x)) j U + Primary.allocate h (ballast _ _ (f y)) j U
    unfold Primary.allocate; split; swap; exact (add_zero (0:ℂ)).symm
    unfold ballast; split
    · rw [show f (x+y) U=f x U+f y U from congr_fun (he.map_add ..) _, add_mul]
    exact (add_zero _).symm
  intro i x; refine Prod.ext rfl (Prod.ext (smul_zero i).symm ?_)
  funext j U; change Primary.allocate h (ballast _ _ (f (i • x))) j U=i*Primary.allocate h (ballast _ _ (f x)) j U
  unfold Primary.allocate; split
  · unfold ballast; split
    · rw [show f (i • x) U = i*f x U from congr_fun (he.map_smul ..) _,mul_assoc]
    exact (mul_zero _).symm
  exact (mul_zero i).symm

/-- Probe startup bill test at stage m. -/
def openingFee (C : Family G) (d m : ℕ) :=
    liftFee (C.localSection d).stencil.card *
      (Real.exp (C.path.levels.params m).supportExponent * (Maquette.upper (C.localSection d)*(Single.excess C d m)))

set_option maxHeartbeats 800000
-- charged at base
lemma arrival (H : C.Makes) (o : Site (C.side m p)) (X : ℕ→Support (C.side m p)) (hX : ∀ i,o∈X i)
    (h : Room (C.path.rep N p m)) (hi : m≤N) (hY : Maquette.room (C.localSection d) ≤ C.path.levels.clock.coverSize m)
    (hF : money C.path.levels m*openingFee C d m ≤ 1) (v : C.label d) :
    let F := C.labels.level d; let P := C.path.rep N p m; let S := C.localSection d
    let Q := address X (beginAt S o h v)
    Q.Format o C.params P ∧ Q.remBound o P (money C.path.levels m) (F.coeffSize (F.core v)) ∧ Q.regular=0 ∧ Q.x=v ∧
    ∀ U,Q.density o S P U= ((C.S.a m:ℂ)^d) * ((C.path.rep N p m).eval U:ℂ) * initial S (Match.view C.path N) m p v o U := by
  intro F P S Q
  let L := C.path.levels; let κ := money L m; let w := L.clock.forcedAllowance m; let R := F.coeffSize (F.core v); let t := P.p.threshold
  let Z := kit S o t v
  let K := S.footprint o
  have hR : 0≤R := Work.G08.size_nonneg ..
  obtain ⟨hκ,hκ'⟩ := (money_accepted L m : 0<κ ∧ κ≤1)
  have hp := (H.wilson.represents N p m hi).good
  have hL : P.p=L.budget m := (H.wilson.represents N p m hi).vac
  let g := Single.excess C d m
  let a := Maquette.upper S
  have hA := H.sections d
  have hZ : Weight P.p K (Z.tail P) := kit_copies S o v hA
  have hg := Single.excess_one C d m
  have ha : 1 ≤ a := (Maquette.purposes S 0).1
  have hv U : ‖Z.seen U‖ ≤ a*g*R := by unfold Z kit t; rw [hL]; exact Maquette.maximum S _ (potential_hat L m).1 _ (potential_hat L m).2 o _ _
  have hz U : ‖Z.tail P U‖ ≤ a*g*R := by unfold Z t; rw [tail_is,Pi.sub_apply]; by_cases he : Healthy P.p.threshold K U
                                         · rw [masked_eq _ _ _ _ he,sub_self,norm_zero]; change 1≤g at hg; positivity
                                         rw [masked_ne _ _ _ _ he,sub_zero]; exact hv _
  obtain hiw : w = κ^2 := (Real.sq_sqrt (Real.exp_pos _).le).symm
  have hw : 0<w := Real.exp_pos _
  have hW : w≤1 := by rw [hiw]; nlinarith only [hκ,hκ']
  obtain ⟨f,hf,hU⟩ := merge_bound P (fun _ : Unit => K) {()} (singleton_nonempty _) (r:=0) le_rfl hw.le hW
    (Alphabet.mint_zero P hp.labels) S.stencil.card (fun _ => card_image_le) (fun _ => Z.tail P) (fun _=>a*g*R)
    (by change 1≤g at hg; intro i; positivity) (fun _ => hz)
  rw [prod_singleton] at hf
  let B := ballast K P (Z.tail P)
  have he (q : Pack (C.side m p)) U : B q U=payload (fun _ : Unit => K) P (fun _=>Z.tail P) {()} q U := (single_payload (fun _ : Unit => K) P (fun _=>Z.tail P) q () U).symm
  have hh q := Primary.credible P K (Z.tail P) hZ hp.labels q
  have hvalid := Primary.wrapped h B (fun q => (hh q))
  have hor : o∈K := mem_image.mpr ⟨0,hA.anchored,by simp⟩
  have hF' : Q.Format o C.params P := ⟨fun i => (null_path ..).1,hX,fun _=>rfl,
      fun i hh J => ⟨contDiffAt_const,fun j _ => by change iteratedDeriv j (0:ℝ→ℂ) 0=0; simp⟩,
      fun i => (hvalid i).2.2.2.2,fun i h => (hvalid i).2.2.2.1 h hor,fun i => (hvalid i).1,
      fun i => (hvalid i).2.1,fun i => (hvalid i).2.2.1⟩
  obtain ⟨x,hx,hS⟩ := Primary.expenses h B (r:=0) (c:=κ*R) (by
    refine ⟨f,hf.trans ?_,fun i => ⟨(hU i).1,fun U => (he i U) ▸ (hU i).2 U⟩⟩
    have hϕ := (L.budget m).exponent_pos
    let r := liftFee S.stencil.card
    have hr : 0≤r := (lift_pos _).le
    have ht : burn P.p 0 ((fun _ : Unit=>K) ()) ≤ Real.exp ((L.budget m).supportExponent) := by
      unfold burn; rw [add_zero,hL]; refine Real.exp_monotone (mul_le_of_le_one_right hϕ.le ?_)
      exact_mod_cast (show coverNumber (L.budget m).B K≤1 from Maquette.hoist S o _ hY)
    change 1 ≤ g at hg
    calc
      _ ≤ w * (r * (Real.exp ((L.budget m).supportExponent)*(a*g*R))) := by change w*(r*(_*_)) ≤ _; gcongr
      _ = κ*(κ* openingFee C d m *R) := by rw [hiw]; change κ^ _ * (r*(_*(_*R)))=κ*(κ*(r*(_*(a*g)))*R); dsimp only [L,Levels.budget]; ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left ((mul_le_mul_of_nonneg_right hF hR).trans_eq (one_mul _)) hκ.le)
  have hhome : Q.remBound o P κ R := ⟨0,R,le_rfl,hR,(zero_add _).le,hκ, ⟨0,by simp [SumBudget,BudgetPoint.mass],fun i => (null_path ..).2 _⟩,x,by simpa only [burn_zero] using hx,hS⟩ 
  refine ⟨hF',hhome,rfl,rfl,fun U => ?_⟩
  rw [← BranchOne.present Q _ o hp hhome]
  have H : BranchOne.center Q S o P=Z.birth P := by
    apply Prod.ext
    · funext U; change _+_+(∑' i : ℕ,masked P.p.threshold (X i) ((0:ℕ→ Config G (C.side m p)→ℂ) i) U)=_ ; simp only [Pi.zero_apply]; simp [masked]; rfl
    funext q U; exact Primary.allocation h B U q
  rw [H,birth_tangent P Z hp.labels hZ, complete_kit S o hA]
  unfold initial
  have hα := C.S.a_pos m
  have hy : (C.S.a m:ℂ)≠0 := by exact_mod_cast hα.ne'
  have hv' : (Match.view C.path N).S.a m=C.S.a m := rfl
  rw [Pi.smul_apply,smul_eq_mul,hv',show (Match.view C.path N).levels.clock.threshold m=t from congrArg BudgetPoint.threshold hL.symm]
  field_simp; rfl
end YM.AnalyticNext.GridStop.Coarrival
