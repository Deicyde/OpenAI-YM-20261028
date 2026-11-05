import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Capital
import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Clerk


set_option warningAsError false

/-! # Reframe an arbitrary singleton response along C's path -/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.GridStop.Primary
open Function Filter MeasureTheory RG Wilson Lattice Marker Overlay Source Bid Labels Multi Finset
open Multi.Couples Pair
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G : Gauge} {C : Family G} {m p d N : ℕ} {o : SiteSpace C m p} {r κ b μ : ℝ}
    {Z : Pulse G (C.side m p)} {P : Rep G (C.side m p)}
    (Y : Folio C o Z.1 d r b)

def law (C : Family G) {m p} (o : SiteSpace C m p) (d : ℕ) (r : ℝ) := (wage C d m * fence C o d r) + (1+endowment C o d r)

/-- Extraction recipe from a signed ONE variation at o, including a finite
assignment replacing Z.2 Compressed. The readout agreement even survives
an alphabet-dependent local estimate. -/
def frame (hP : Room P) : Coefficient (C.labels.level d) (C.side m p) :=
  ⟨voice Y,patch Y,page Y, allocate hP (Z.2+investments Y P)⟩

lemma moves (hP : Room P) (h : Credit P.p (r+2) κ {o} Z b) (he : P.p=C.path.levels.budget m) (hr : 0 ≤ r)
    (hC : C.Makes) (hF : Priced Y P κ) :
    (frame Y hP).Format o C.params P ∧ (frame Y hP).remBound o (funds P r hr) κ (law C o d r * b) := by
  let K := frame Y hP
  let T := Z.2+investments Y P
  obtain ⟨-, -,hκ,hb,-,L,hL,hT⟩ := h
  obtain ⟨hh,hj⟩ := assigned Y P hr hF
  have hQ (i : Pack (C.side m p)) : Legible P.p i (T i) ∧ (T i ≠ 0 → ({o}:Support _) ⊆ i.zone) := by
    refine ⟨(hT i).1.add ((hj i).1),fun hc => ?_⟩
    by_cases he : investments Y P i=0
    · unfold T at hc; rw [Pi.add_apply,he,add_zero] at hc; exact (hT i).2.1 hc
    exact singleton_subset_iff.mpr ((hj i).2.1 he)
  have hx := wrapped hP T hQ
  let B := wage C d m
  let F := fence C o d r
  let J := 1+endowment C o d r
  have hB : 0 ≤ B := zero_le_one.trans (wage_one ..)
  have hW : 0 ≤ B*F := mul_nonneg hB (burn_pos ..).le
  refine ⟨⟨fun i => he.symm ▸ (Y.path i).2.1,fun i => mem_union_left _ (Y.anchored i),fun i => (Y.path i).2.2.1,
      fun i => (Y.path i).2.2.2.1,fun i => (hx i).2.2.2.2,fun i hh => (hx i).2.2.2.1 hh (mem_singleton_self _),fun i =>
      (hx i).1,fun i => (hx i).2.1,fun i => (hx i).2.2.1⟩, B*F*b,J*b, mul_nonneg hW hb,
      mul_nonneg (add_nonneg zero_le_one endowment_price) hb,?_,hκ, ?_, ?_⟩
  · unfold B F J law; apply le_of_eq; ring
  · have hl (V : Support (C.side m p)) (x : ℝ) (h : 0 ≤ x) :
        0 ≤ (funds P r hr).p.mass V x ∧ (funds P r hr).p.mass V x ≤ burn P.p (r+2) V * x := by
      unfold BudgetPoint.mass funds; exact ⟨mul_nonneg (Real.exp_pos _).le h,mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right
        (by dsimp only; linarith) (by exact_mod_cast Nat.zero_le _))) h⟩
    refine ⟨fun i => B * Y.fee i,permit_le (rem_budget Y P hr he hC) le_rfl (fun i => hl _ _ (mul_nonneg hB (Y.pay _))),?_⟩
    intro i; change P.p.supBounds _ _ _ _; rw [he]; exact (Y.path i).2.2.2.2.1
  have hg : ∃ A : Pack (C.side m p)→ℝ, (∑ i : Pack (C.side m p),burn P.p r i.zone*A i) ≤ κ*(J*b) ∧ ∀ i,0 ≤ A i ∧ ∀ U,‖T i U‖≤A i := by
    refine ⟨fun i => L i+∑' j,hF.fee j i,?_,fun i => ⟨add_nonneg (hT i).2.2.1 (hj i).2.2.1,fun U => (norm_add_le
      (Z.2 i U) _).trans (add_le_add ((hT i).2.2.2 U) ((hj i).2.2.2 U))⟩⟩
    have hw : (∑ i : Pack (C.side m p),burn P.p r i.zone*L i) ≤ κ*b :=
      le_trans (Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (Real.exp_monotone (mul_le_mul_of_nonneg_right
        (le_add_of_nonneg_right (b:=2) (by norm_num) |>.trans_eq (add_assoc ..)) (by exact_mod_cast Nat.zero_le _))) ((hT i).2.2.1)) hL
    simp_rw [mul_add, Finset.sum_add_distrib]; unfold J; apply (add_le_add hw hh).trans_eq; ring
  obtain ⟨f,hf,hF⟩ := expenses hP T hg
  exact ⟨f,hf,hF⟩

/-- Why the recentering method will work through a whole *mixed* tangent
editing scheme (see Alphabet). Here at the Coefficient level. Do NOT identify
tangents on JUST the mask/test cells at o. -/
theorem scheme (hr : 0 ≤ r) (hP : Room P) (he : P.p=C.path.levels.budget m) :
    let S := C.localSection d; let R : Pulse G (C.side m p) := BranchOne.center (frame Y hP) S o P
    R.1 = Z.1 - (fun U => ∑' i,hole Y i U) ∧ R.2 = Z.2 + investments Y P := by
  dsimp only
  constructor
  · funext i; have hh := (eq_sub_of_add_eq (expression Y hr i).symm)
    change (frame Y hP).exponentialEntry o _ P i = _-_ -- pointwise
    unfold Coefficient.exponentialEntry Coefficient.maskedTerm; rw [he]; exact hh
  funext q U; exact allocation hP (Z.2+investments Y P) U q

lemma centerMoves (hr : 0 ≤ r) (hP : Room P) (he : P.p=C.path.levels.budget m) (hF : Priced Y P κ) {τ w : ℝ}
    (hV : P.activities.Valid P.p τ w) :
    tangent P (BranchOne.center (frame Y hP) (C.localSection d) o P) = tangent P Z := by
  let Q := BranchOne.center (frame Y hP) (C.localSection d) o P
  let H := fun U => ∑' i,hole Y i U
  have hh : Q=(Z+(((-H: Config G _→ℂ),investments Y P):Pulse G _)) := Prod.ext
    ((scheme Y hr hP he).1.trans (by change Z.1 - H = Z.1 + -H; rw [sub_eq_add_neg])) ((scheme Y hr hP he).2
      : Q.2 = Z.2+_)
  have hg : (((-H: Config G _→ℂ),investments Y P):Pulse G _) = (-H,0)+(0,investments Y P) :=
    Prod.ext (add_zero _).symm (zero_add _).symm
  change tangent P Q=_
  rw [hh,hg, Alphabet.tangent_add,Alphabet.tangent_add]
  funext U; have HB := credited Y P hr he hF U hV
  simp only [Pi.add_apply,HB]
  rw [show tangent P ((- H : Config G _→ℂ),0) U = - (P.eval U:ℂ)*∑' i,hole Y i U from ?_] -- rename to avoid conflict
  · rw [neg_mul]; ring
  unfold tangent; simp only [Pi.zero_apply, zero_mul,Finset.sum_const_zero,mul_zero,add_zero,
    Pi.neg_apply]; rw [mul_neg,neg_mul]

/-- Uniform primary extraction from a probe output above the true
calibration stencil, with a higher exponent payment through Pack and without
paying inverse powers of threshold on coordinates even for flag/clusters.
Analog . Export explicit choices & alignment. This uses and does
not produce the required RG histories. Because the stencil contribution
in regular payments is only ONE cover unit when ready for RG, these
prices can be bought through a log β budget (or ordinary P powers) per
invocation, not assuming fixed block or fixed period. -/
theorem manifest {o : SiteSpace C m p} (hP : Room P) (h : Credit P.p (r+2) κ {o} Z b) (he : P.p=C.path.levels.budget m) (hr : 0 ≤ r)
    (hC : C.Makes) (hi : C.ref d ≤ m) {x t e τ w : ℝ} (hL : P.Lawful t x e τ w) (hm : Mint P r μ)
    (hμ : μ ≤ κ) (hB : cells P.p*μ≤1) :
    ∃ Q : Coefficient (C.labels.level d) (C.side m p), Q.Format o C.params P ∧ Q.remBound o (funds P r hr) κ (law C o d r * b) ∧
      (C.labels.level d).coeffSize Q.x ≤ (1+patron C d)*b ∧ Q.density o (C.localSection d) P=tangent P Z ∧
      ∃ Y : Folio C o Z.1 d r b,Q=frame Y hP ∧
      let R := BranchOne.center Q (C.localSection d) o P
      (R.1=Z.1-(fun U => ∑' i,hole Y i U)) ∧ R.2=Z.2+investments Y P ∧ Nonempty (Priced Y P κ) := by
  have hd : Nonempty (Folio C o Z.1 d r b) := by
    apply book hC hi; rw [←he]
    obtain ⟨a,e,ha,-,hw,hT⟩ := h.2.2.2.2.1
    exact ⟨a,e,ha,hw,hT⟩
  obtain ⟨Y⟩ := hd
  obtain ⟨I⟩ := premium Y P hr he hC hm hB hμ hL.labels
  obtain ⟨hf,hc⟩ := moves Y hP h he hr hC I
  refine ⟨frame Y hP,hf,hc,each_price Y hr,?_,Y,rfl,(scheme Y hr hP he).1,(scheme Y hr hP he).2,⟨I⟩⟩
  rw [← BranchOne.present _ _ o hL (funds_erases hr hc)]
  exact centerMoves Y hr hP he I hL.labels
end YM.AnalyticNext.GridStop.Primary
