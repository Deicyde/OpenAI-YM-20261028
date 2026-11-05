import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Words
import YM.ProjectorNext.PROJECTOR_CALIBRATION.Germ

/-!
# Actual kpc perturbations of the unmasked calibration

For a fixed **slot list** and Lens compare linearization with the true old t
reading. Constants may be assessed before the tori (uses projected germs
at origin), but still need affordability with the actual k/list lengths.
Also costs of full Wick self-contractions. This is local; no small-margin
assumptions on the transmitted x through scales.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Further.CorrectedLift
open Filter Function Lattice Wilson RG Source Source.Drops Labels Next.Extract Extraction
open Push.Corrected Push.Corrected.Issue Push.CutoffProjectors Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff
variable {G : Gauge} {C : Family G} {d m p N t l s : ℕ}

namespace Scratch
open YM.ProjectorNext.Calibration.Coupon
variable (H : Hol G) (W : Fin s → Slot) (w : Fin l → Fin s × G.ColorIndex) (a : Lens G d)

def report (Y : Panel G s) := ∏ i, (↑(Y (w i).1 (w i).2) : ℂ)

def compareAt (z : ℝ) :=
    let A := bring H d W
    iteratedDeriv a.2.val (fun r => report w (trim d A z (trunk d (scaleJet a.1 r)))) 0

lemma nice : ContDiff ℝ ω (report w) := by
  unfold report; refine contDiff_prod (𝕜:=ℝ) ?_
  intro i _; exact Complex.ofRealCLM.contDiff.comp ((EuclideanSpace.proj (w i).2).contDiff.comp (contDiff_apply ℝ G.Color _))
lemma smooth : ContDiff ℝ ω (compareAt H W w a) := by
  let Z (r : ℝ) := trunk d (scaleJet a.1 r)
  let f (x : ℝ × ℝ) := report w (trim d (bring H d W) x.1 (Z x.2))
  have h : ContDiff ℝ ω Z := Board.trunk_nice a.1
  have he : ContDiff ℝ ω f := (nice w).comp ((trim_smooth d (bring H d W)).comp
    (f:=fun x : ℝ × ℝ => (x.1,Z x.2)) (contDiff_fst.prodMk (h.comp contDiff_snd)))
  exact varies _ he

lemma connected (z : ℝ) (hz : 0 < z) :
    iteratedDeriv a.2.val (fun u => report w
      (z⁻¹ • bring H d W (trunk d (scaleJet (z • a.1) u)))) 0=compareAt H W w a z := by
  let T := bring H d W
  let f (Y : Panel G s) := report w (z⁻¹ • Y)
  have hT : ContDiffAt ℝ ω T 0 := contDiffAt_pi.mpr fun i => ((Board.pegs H d).shot (W i)).contDiffAt
  have hf : ContDiff ℝ ω f := (nice w).comp (show ContDiff ℝ ω (fun Y : Panel G s => z⁻¹ • Y) from
    (ContinuousLinearMap.contDiff (f:=(z⁻¹ • ContinuousLinearMap.id ℝ (Panel G s)))))
  have he (u : ℝ) : trunk d (scaleJet (z • a.1) u) = z • trunk d (scaleJet a.1 u) := by
    funext i; exact smul_comm (u^(i.val+2)) z (a.1 i.val)
  simp_rw [he]; change iteratedDeriv a.2.val (fun h => f (T _)) 0 = _
  have hg := exchanged d (Nat.le_of_lt a.2.isLt) z hT hf (Board.trunk_nice (d:=d) a.1) (Board.trunk_zero a.1)
  rw [hg]; simp_rw [show T 0=0 from funext fun i => takes_zero H d _, zero_add]
  simp only [f,inv_smul_smul₀ hz.ne']; rfl

lemma core (X : Snap G d) : trim d (bring H d W) 0 X = fun i => Blurb H d (W i) X := by
  funext i; rw [trim_value]
  let A := bring H d W
  have ht j : DifferentiableAt ℝ (takes H d (W j)) 0 := ((Board.pegs H d).shot _).differentiableAt
  unfold bring; rw [fderiv_pi ht]; rfl

private theorem sharp : ∃ c : NNReal,
    LipschitzOnWith c (compareAt H W w a) (Set.Icc 0 1) := by
  exact (smooth ..).contDiffOn.exists_lipschitzOnWith (by simp) (convex_Icc ..) isCompact_Icc

def ceilings (x : ℝ) : Prop := 0 ≤ x ∧ ∀ z∈Set.Icc (0:ℝ) 1,
    ‖compareAt H W w a 0 - compareAt H W w a z‖ ≤ x*z

lemma caps : ∃ x : ℝ, ceilings H W w a x := by
  obtain ⟨b,hb⟩ := sharp H W w a
  refine ⟨b,NNReal.coe_nonneg _,fun z hz => ?_⟩
  rw [← dist_eq_norm]
  apply (hb.dist_le_mul 0 (Set.left_mem_Icc.mpr zero_le_one) z hz).trans_eq
  rw [dist_zero_left, Real.norm_of_nonneg hz.1]

def scratch : ℝ := sInf (ceilings H W w a)


lemma upper {z : ℝ} (hz : z∈Set.Icc (0:ℝ) 1) :
    ‖compareAt H W w a 0 - compareAt H W w a z‖ ≤ scratch H W w a*z := by
  by_cases ht : 0 < z
  · apply (div_le_iff₀ ht).1
    exact le_csInf (caps ..) fun _ (h : ceilings H W w a _) => (div_le_iff₀ ht).2 (h.2 z hz)
  obtain rfl : z=0 := le_antisymm (le_of_not_gt ht) hz.1
  simp
end Scratch

-- factorial derivative pricing is on the full frame (no assumed rank).
def probeJet (a : Lens G d) : Pol G →ₗ[ℂ] ℂ :=
    (a.2.val.factorial:ℂ) • ((Labels.read a.1).toLinearMap.comp (tier a.2.val))
lemma probeJet_value (a : Lens G d) (u : Pol G) :
    probeJet a u=iteratedDeriv a.2.val (fun x => Labels.read (scaleJet a.1 x) u) 0 := by
  rw [deriv_read]; simp [probeJet,Complex.real_smul]

namespace Screen
variable (B : Screen C m p t)

def chip (b : Lens G d) (w : B.Word l) := Scratch.scratch C.params B.leg w b
lemma receipt (a : Lens G d) (w : B.Word l) :
    ‖probeJet a (B.string d 1 w ∅) - B.full C.params a w‖ ≤ B.chip a w * θ C m := by
  let H := C.params; let z := θ C m
  have hz := Scratch.upper H B.leg w a (z:=z) (show z∈Set.Icc _ _ from
    ⟨(C.path.levels.budget m).threshold_pos.le,(C.path.levels.budget m).threshold_le⟩)
  have hT : Scratch.compareAt H B.leg w a z=B.full C.params a w := by
    rw [← Scratch.connected H B.leg w a z (C.path.levels.budget m).threshold_pos]
    unfold Board.full
    rw [show B.detect w ∘ B.sheet C.params a= _ from ?_]
    funext u
    change B.detect w _=B.detect w _
    apply congr_arg (B.detect w); exact funext fun _ => B.asCover ..
  have h0 : Scratch.compareAt H B.leg w a 0=probeJet a (B.string d 1 w ∅) := by
    rw [probeJet_value]; unfold Scratch.compareAt string
    simp_rw [Scratch.core,Loop.loose_empty,Complex.ofReal_one, one_smul,map_prod,read_slot]; rfl
  rw [←h0,←hT]; exact hz

variable (Q : Copper G (C.side m p))

def charge (w : B.Word l) (A : Loop.Pairs l) (a : Lens G d) :=
    (∏ b∈A,(4:ℝ)*‖cost B Q w b‖)*‖probeJet a (B.string d 1 w A)‖

lemma bound_toll (h : C.Makes) (e : m≤N) (w : B.Word l) (A : Loop.Pairs l) (hp : A.Nonempty) :
    ‖∏ b∈A, toll B Q N w b‖ ≤ (2/C.path.levels.clock.monitor m ^ 2)*(∏ b∈A,(4:ℝ)*‖cost B Q w b‖) := by
  let Z := C.path.levels.clock.monitor m; let z : ℝ := 2/Z^2
  have hr := ratio_pos h p e
  have he b : ‖B.toll Q N w b‖ = ratio C m N p ^2 * ‖B.cost Q w b‖ := by
    simp_rw [toll,norm_mul, Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg hr.le]
  have hZ : 0<Z := Real.exp_pos _
  have hz : 0<z := by unfold z; positivity
  have hh : ratio C m N p ^2 ≤ z := (le_div_iff₀ (by positivity)).2 (ratio_budget h p e).2
  have hu : ratio C m N p ^2 ≤ 4 := by nlinarith [(ratio_crude h p e).1]
  obtain ⟨b,hb⟩ := hp
  rw [norm_prod]
  conv_lhs => rw [← Finset.mul_prod_erase A _ hb, he b]
  conv_rhs => rw [← Finset.mul_prod_erase A _ hb,←mul_assoc]
  refine mul_le_mul ?_ ?_ (Finset.prod_nonneg fun _ _ => norm_nonneg _) ?_
  · refine (mul_le_mul_of_nonneg_right hh (norm_nonneg _)).trans ?_
    exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left (norm_nonneg _) (by norm_num)) hz.le
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun j _ => by rw [he]; exact mul_le_mul_of_nonneg_right hu (norm_nonneg _)
  exact mul_nonneg hz.le (by positivity)

def spare (_ : B.Word l) := (Loop.joins (Finset.univ (α:=Fin l))).erase ∅

def costAt (a : Lens G d) (w : B.Word l) :=
    B.chip a w * θ C m + 2/C.path.levels.clock.monitor m ^ 2 * ∑ A∈B.spare w, charge B Q w A a


theorem rung (h : C.Makes) (e : m≤N) (a : Lens G d) (w : B.Word l) :
    ‖probeJet a (B.meters Q 1 d N w)-B.full C.params a w‖ ≤ B.costAt Q a w := by
  let L := Loop.joins (Finset.univ (α:=Fin l))
  let I := L.erase ∅
  let U (A : Loop.Pairs l) := probeJet a (B.string d 1 w A)
  let V b := B.toll Q N w b
  let W (A : Loop.Pairs l) := (∏ b∈A,V b)*U A
  have he : probeJet a (B.meters Q 1 d N w)-B.full C.params a w=(U ∅-B.full C.params a w)+(∑ A∈I,W A) := by
    simp_rw [meters,map_sum,map_smul]; change (∑ x∈L,W x)-_= _
    rw [← Finset.add_sum_erase _ W (show ∅∈L from Loop.empty_in _),show W ∅=U ∅ from by simp [W]]; ring
  rw [he]; apply (norm_add_le ..).trans; apply add_le_add (B.receipt a w); apply (norm_sum_le ..).trans
  rw [Finset.mul_sum]; apply Finset.sum_le_sum; intro b hb
  unfold W; rw [norm_mul]
  apply (mul_le_mul_of_nonneg_right (B.bound_toll Q h e w b (Finset.nonempty_iff_ne_empty.mpr (Finset.ne_of_mem_erase hb))) (norm_nonneg _)).trans_eq
  rw [charge]; unfold U; ring

def bill (a : Lens G d) : ℝ := ∑ w : B.All,B.ink d w.fst.val * B.costAt Q a w.snd
lemma each_price (h : C.Makes) (v : C.label d) (e : Resolution C d N B) (a : Lens G d) :
    ‖probeJet a (B.rows Q 1 v N) - probe (C.labels.level d) a (Issue.primary C v m N p)‖ ≤
      B.bill Q a * ‖Issue.primary C v m N p‖ := by
  rw [← reproduces v h e a, rows,map_sum,←Finset.sum_sub_distrib]; apply (norm_sum_le ..).trans
  rw [bill,Finset.sum_mul]; refine Finset.sum_le_sum fun w _ => ?_
  rw [map_smul,smul_eq_mul,←mul_sub,norm_mul,mul_right_comm]
  exact mul_le_mul (B.writes h e v (Nat.le_of_lt_succ w.fst.isLt) w.snd) (B.rung Q h e.covered a w.snd) (norm_nonneg _)
    (mul_nonneg (B.ink_pos) (norm_nonneg _))
end Screen
end YM.Further.CorrectedLift
