import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Hist
import YM.Push.CUTOFF_PROJECTORS.Bank
/-!
# The full holonomy side before wick/linear comparison
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Source Source.Drops Labels Next.Extract Extraction Work
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {n : Side} {X : Support n} {P : BudgetPoint} {f : Config G n → ℂ} {d m p N t l : ℕ}

-- all component words, occurrence not plaquette name
namespace Board
variable (B : Board G n P t)
def detect (w : B.Word l) (Y : B.Eye) : ℂ := ∏ i, (↑(Y (w i).1 (w i).2) : ℂ)

lemma detect_nice (w : B.Word l) : ContDiff ℝ ω (B.detect w) := by
  unfold detect; refine contDiff_prod (𝕜:=ℝ) ?_
  intro i _; exact Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (w i).2).contDiff.comp (contDiff_apply ℝ G.Color _))

lemma splitEye (Y : B.Eye) : Y = ∑ b : B.Bit, (Y b.1 b.2) • B.blade b := by
  symm; unfold Bit; rw [Fintype.sum_prod_type]
  funext i; rw [Finset.sum_apply,Finset.sum_eq_single i]
  · simp only [blade,Finset.sum_apply,Pi.smul_apply,Pi.single_eq_same]; exact (EuclideanSpace.basisFun G.ColorIndex ℝ).sum_repr (Y i)
  · intro j _ hj; simp only [blade,Finset.sum_apply,Pi.smul_apply,Pi.single_eq_of_ne hj.symm,smul_zero,Finset.sum_const_zero]
  simp

lemma allEyes (T : Tensor.T B.Eye ℂ l) (Y : B.Eye) :
    (∑ w : B.Word l, T (fun i => B.blade (w i)) * B.detect w Y) = Tensor.diagonal T Y := by
  let F (b : B.Bit) := (Y b.1 b.2) • B.blade b
  trans ∑ w : B.Word l, T fun i => F (w i)
  · refine Finset.sum_congr rfl fun w _ => ?_
    unfold F detect; rw [T.map_smul_univ,Complex.real_smul, Complex.ofReal_prod]; exact mul_comm ..
  rw [show ∑ w : B.Word l, T _ = T (fun _ => ∑ b : B.Bit,F b) from (T.toMultilinearMap.map_sum (fun _ (b:B.Bit) => F b)).symm]
  simp_rw [show ∑ b : B.Bit,F b=Y from (B.splitEye Y).symm]; rfl

-- bs in the t-scaled representation sum, original transports
lemma views (Y : B.Eye) :
    ∑ w : B.All, B.print f w.1.val w.2 * B.detect w.2 Y = G05.blockTaylor t (f ∘ B.showAt) Y := by
  unfold All; rw [Fintype.sum_sigma]
  simp_rw [Board.print,B.allEyes]; rw [G05.blockTaylor,Finset.sum_apply ]
  exact Fin.sum_univ_eq_sum_range (fun j => Tensor.diagonal (Tensor.coeff (f ∘ B.showAt) j 0) Y) _

lemma pegs (H : Hol G) (d : ℕ) : Peg H d := Work.G02.answer Work.G01.answer G H d

def sheet (H : Hol G) (i : Lens G d) (r : ℝ) : B.Eye := B.input (H.testLinks d (0:Site n) (P.threshold • i.1) r)

lemma trunk_zero (J : Jet G) : trunk d (scaleJet J 0) = 0 := by ext1 j; simp [trunk,scaleJet]
lemma trunk_nice (J : Jet G) : ContDiff ℝ ω (fun s => trunk d (scaleJet J s)) := by
  apply contDiff_pi.mpr; intro i
  have h {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (a : ℕ) (c : X) :
      ContDiff ℝ ω (fun t : ℝ => t^a • c) := (contDiff_id.pow _).smul contDiff_const
  exact h (i.val+2) (J i.val)

lemma asCover (H : Hol G) (i : Lens G d) (r : ℝ) (j) :
    B.sheet H i r j = P.threshold⁻¹ • takes H d (B.leg j) (trunk d (scaleJet (P.threshold • i.1) r)) := by
  rw [sheet,B.full_cover]; change P.threshold⁻¹ • (B.leg j).eval (H.links d _ r) = _
  rw [scales]; rfl

@[simp] lemma sheet_zero (H : Hol G) (i : Lens G d) : B.sheet H i 0=0 := by
  funext j; rw [B.asCover,trunk_zero, takes_zero,smul_zero]; rfl
lemma sheet_diff (H : Hol G) (i : Lens G d) : ContDiffAt ℝ ω (B.sheet H i) 0 := by
  refine contDiffAt_pi.mpr fun j => ?_
  simp_rw [B.asCover]
  let A := (fun s => trunk d (scaleJet (P.threshold • i.1) s))
  have he : A 0=0 := trunk_zero (P.threshold • i.1)
  have hz : ContDiffAt ℝ ω (takes H d (B.leg j)) (A 0) := by rw [he]; exact ((pegs H d).shot _).contDiffAt
  have hv : ContDiff ℝ ω A := trunk_nice (P.threshold • i.1)
  have hr := hz.comp (0:ℝ) (f:=A) hv.contDiffAt
  exact (contDiffAt_const (c:=P.threshold⁻¹)).smul hr

def full (H : Hol G) (i : Lens G d) (w : B.Word l) := iteratedDeriv i.2.val (B.detect w ∘ B.sheet H i) 0

lemma one_history (H : Hol G) (hx : P.Regular X f) (hX : X⊆B.cube) (hd : d≤t) (ht : t ≤ P.order) (i : Lens G d) :
    ∑ w : B.All, B.print f w.1.val w.2 * B.full H i w.2 =
      iteratedDeriv i.2.val (f ∘ H.testLinks d (0:Site n) (P.threshold • i.1)) 0 := by
  let F := f ∘ B.showAt
  let A := G05.blockTaylor t F
  let L := B.sheet H i
  have hd' : i.2.val ≤ t := (Nat.le_of_lt_succ i.2.isLt).trans hd
  have Hf : ContDiffAt ℝ t F 0 := B.smooth hx ht le_rfl
  have HA : ContDiff ℝ t A := G05.blockTaylor_contDiff ..
  have hL : ContDiffAt ℝ (↑t:WithTop ℕ∞) L 0 := (B.sheet_diff H i).of_le le_top
  have hz : L 0=0 := B.sheet_zero H i
  have hQ := G05.jets_comp (d:=t) hL hL HA.contDiffAt (show ContDiffAt ℝ t F (L 0) from hz.symm ▸ Hf)
    rfl (fun _ _ => rfl) (hz.symm ▸ G05.blockTaylor_jets Hf) _ hd'
  rw [(show f ∘ H.testLinks d (0:Site n) (P.threshold • i.1) =ᶠ[𝓝 0] F ∘ L from B.same H (P.threshold • i.1) d hx hX).iteratedDeriv_eq (n:=i.2.val)]
  change _ = iteratedDeriv i.2.val (F ∘ L) 0
  trans iteratedDeriv i.2.val (A ∘ L) 0
  · rw [show A ∘ L = fun x => ∑ w : B.All, B.print f w.1.val w.2 * B.detect w.2 (L x) from
      funext fun x => (B.views (L x)).symm, iteratedDeriv_fun_sum]
    · apply Finset.sum_congr rfl; intro _ _; rw [iteratedDeriv_const_mul_field]; rfl
    exact fun j _ => contDiffAt_const.mul (((B.detect_nice j.2).of_le le_top).contDiffAt.comp _ (hL.of_le (Nat.cast_le.mpr hd')))
  exact congr_arg (fun T : Tensor.T ℝ ℂ i.2.val => T fun _ => (1:ℝ)) hQ
end Board

namespace Screen
variable {C : Family G} (v : C.label d) (h : C.Makes) {B : Screen C m p t}
  (hr : Resolution C d N B)
include hr h

lemma article (a : Lens G d) (j : ℕ) (hj : short C d m N p j) :
    ∑ w : B.All, B.print (annal C v m N p j) w.1.val w.2 * B.full C.params a w.2 = 0 := by
  rw [B.one_history C.params (annal_ok h hr.respects hr.covered p v j) (hr.news j hj) hr.orders hr.affordable]
  let R := chunk C v m N p
  have H : R.Format 0 C.params (C.path.rep N p m) := (h.calibrated _ _ p (hr.respects.trans hr.covered)).format m hr.respects hr.covered _
  have hu : R.support j=paper C d m N p j := (paper_eq h hr.respects hr.covered j p v).symm
  have e := H.projects j (fun x hx => hr.nonwrapping x ((hr.news j hj) (hu ▸ hx))) (θ C m • a.1)
  change iteratedDeriv a.2.val (fun x => micro C d m * R.regular j (C.params.testLinks d 0 _ x)) 0 = _
  rw [iteratedDeriv_const_mul_field, e.2 a.2.val (Nat.le_of_lt_succ a.2.isLt),mul_zero]

private lemma bulletin (a : Lens G d) :
    ∑ w : B.All, B.print (printed C v m N p) w.1.val w.2 * B.full C.params a w.2 =
      probe (C.labels.level d) a (Issue.primary C v m N p) := by
  rw [B.one_history C.params (canon_ok (N:=N) h hr.respects p v).1 hr.room hr.orders hr.affordable]
  let F := C.labels.level d
  let T := C.localSection d
  let x := primary C v m N p
  let r := θ C m
  let y := F.scaled r⁻¹ x
  have he := placed_reads T (0:Site (C.side m p)) (h.places d m p hr.respects) (h.sections d) y
  classical
  rw [Reads,if_pos (nonwrapping_placement T _ (h.places _ _ _ hr.respects))] at he
  rw [probe_eq]
  trans iteratedDeriv a.2.val (fun s => Labels.read (scaleJet (r • a.1) s) (F.coords.symm y).val) 0
  · exact (he (r • a.1)).2.2 _ (Nat.le_of_lt_succ a.2.isLt)
  have H (s : ℝ) : Labels.read (scaleJet (r • a.1) s) (F.coords.symm y).val = Labels.read (scaleJet a.1 s) (F.coords.symm x).val := by
    rw [show scaleJet (r • a.1) s = r • scaleJet a.1 s from funext fun j => smul_comm (s^(j+2)) r (a.1 j),
      ← read_frame_scaled, show F.scaled r y=x from F.scaled_inv (C.path.levels.budget m).threshold_pos.ne' x]
  simp_rw [H]; rfl

theorem reproduces (a : Lens G d) :
    (∑ w : B.All, B.notes v N w.2 * B.full C.params a w.2) = probe (C.labels.level d) a (primary C v m N p) := by
  let G (w : B.All) := B.full C.params a w.2
  have he i : ∑ w : B.All, B.news v N i w.2 * G w = 0 := by
    by_cases he : short C d m N p i
    · simp_rw [news,if_pos he]; exact article v h hr a i he
    simp [news,he]
  have hS w : Summable (fun i => B.news v N i w.2 * G w) := ((accounts B h hr v (Nat.le_of_lt_succ w.1.isLt) w.2).1.of_norm).mul_right (G w)
  simp_rw [notes, add_mul,Finset.sum_add_distrib, bulletin v h hr a]
  rw [add_eq_left]
  change ∑ w : B.All,(∑' i,B.news v N i w.2) * G w=_
  simp_rw [← tsum_mul_right]
  rw [← Summable.tsum_finsetSum (fun w _ => hS w)]; simp_rw [he]; simp

omit v in
theorem unit_coefficient (hl : l ≤ t) (w : B.Word l) :
    B.notes (C.refUnit d) N w=if l=0 then 1 else 0 := by
  have hx : primary C (C.refUnit d) m N p=(C.labels.level d).e0 := Issue.primary_unit h d hr.respects hr.covered
  have ha : printed C (C.refUnit d) m N p=1 := by
    unfold printed; rw [hx,Frame.scaled_unit]; funext U; exact congr_fun (h.sections d).unit _
  have ht := accounts B h hr (C.refUnit d) hl w
  have he : (∑' i,B.news (C.refUnit d) N i w)=0 := by
    apply norm_le_zero_iff.mp; refine (norm_tsum_le_tsum_norm ht.1).trans (ht.2.trans_eq (by rw [oil,hx,Extra.Histories.Size.unit_core]; simp [Frame.coeffSize]))
  unfold notes; rw [he,add_zero,ha, Board.print]
  split_ifs with hh
  · subst l; simp [Tensor.coeff]
  unfold Tensor.coeff; rw [show ((1:Config G (C.side m p) → ℂ) ∘ _)=fun _ : B.Eye => (1:ℂ) from rfl,
    iteratedFDeriv_const_of_ne hh]; simp
end Screen
end YM.Further.CorrectedLift
