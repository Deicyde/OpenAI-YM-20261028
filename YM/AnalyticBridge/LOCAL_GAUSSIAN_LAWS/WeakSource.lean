import Mathlib.Analysis.Fourier.Convolution
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Accuracy
import YM.Next.BOUNDARY.Coordinates
import YM.Next.FREE_KERNELS.Amend
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Blocks
import YM.Next.SCHEDULE.Postal
import YM.Push.CUTOFF_PROJECTORS.Along
import YM.Push.CUTOFF_PROJECTORS.Signed
import YM.Push.FREE_RESOLVENT.JetWindows
import YM.SectorNext.GAUSSIAN_SECTOR_CHANGE.Tier
import YM.SectorNext.LARGE_FIELD_REMAINDERS.CollarData


/-!
# Real b estimate for the same change price,  (undifferentiated)

Work with fixed L after Teller's prechoices. Need no fine U near ground,
y may come from all frozen group arguments. Even for unrealizable fine
cost/aisle seeds. For the Φ'/Φ subtractions use the thinned V prices
(uniform EVERYWHERE, not just on Teller.Serves or active addresses).
For the actual Xf and Z use true gauges, anew at EACH endpoint that
purchases D^*F0. No comparison of $Q_{\bar V}$ tangent to the rate
for the k-noise needed for the value price. Reuse LargeField.Affine
only on these same genuine weak inputs. Branches actual. Do not provide
jets/differentiate the mask decisions (separate task
SECTOR_COVARIANCE_JETS). Frozen term kept using the actual patched input,
no Haar domain restriction.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws
open Function Filter Set Lattice Wilson RG Precision Exterior Tree MeasureTheory Metric Matrix
open Bid Pressure Pressure.Tube Pressure.Stores Pressure.Teller Push.SectorMeasure Oriented 
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Wisps LocalJet Motion
open scoped Topology Classical BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {F : Forest S.ratio} {A : Stores S} {x : ℝ}
namespace SourceBill

lemma caps (G : Gauge) (L : Side) (Pt : Teller G) : ∃ D : ℝ, 0 < D ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch.L=L → Pt.Funds S T →
      ∀ V : Config G c, Maximum D T x V := by
  open Work.E04 Work.E03 in
    let a := (Fintype.card Layers2:ℝ)*Pt.C
    let b := (Fintype.card (TypeFace 1):ℝ)*Pt.C
    let d := (Fintype.card Gain:ℝ)*Pt.C
    let C := max 1 (max a (max b d))
    have ha : a ≤ C := le_max_of_le_right (le_max_left ..)
    have hb : b ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_left ..))
    have hd : d ≤ C := le_max_of_le_right (le_max_of_le_right (le_max_right ..))
    have hc0 : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left ..)
    let B := capacity Pt.below
    have hB : 0 < B := capacity_pos _
    let q := G.slopeConstant * Real.log L.val
    refine ⟨2*B*(1+C),by positivity,?_⟩
    filter_upwards [eventually_temp_le q (shift_nonneg G L),eventually_room 0 Pt.below.clip.relaxation Pt.below.clip.radius_pos] with x he hbelow
    simp only [add_zero] at hbelow
    intro c f S T hL hT V
    obtain ⟨M,N,-,h'⟩ := hT.feeds
    have hQ : LaneCounts T.down x (temp x) T.low B S.patch.L.val (id : Site c→Site c) := by
      rw [hT.low]; exact lanes h' le_rfl (Work.E04.temp_nonneg _) S.patch.L.property (fun i j => Nat.le_succ _) hbelow
    refine max_paid hc0.le ?_ ?_ ?_ hQ
    · rw [hT.low]; exact (capacity_ge _).2.2
    · rw [hL]; exact he
    obtain ⟨hm,ho,hf,-⟩ := hT.crosses
    constructor
    · refine anchored_mono (leap_anchored S T.R (radiusB x) V Pt.width.le hf) ?_ ?_
      · rw [← mul_div_assoc]; exact div_le_div_of_nonneg_right ha (by positivity)
      let L' := S.patch.L
      have hl : 0 < (L'.val:ℝ) := Bloch.side_pos _
      calc
        ((Fintype.card (Bloch.Co L' Layers2):ℝ)*(Pt.C / (L'.val:ℝ)^2)) = a*(L'.val:ℝ)^2 := by
          dsimp only [a, Bloch.Co]; rw [Fintype.card_prod,site_card,Nat.cast_mul,Nat.cast_pow]; field_simp
        _ ≤ C*(L'.val:ℝ)^2 := by gcongr
    · exact anchored_mono (lane_anchored T.R.mn (poleEquiv c) (meshEquiv c) (radiusB x) S.patch.L.val S.patch.L.property V Pt.width.le hm) ha hb
    exact anchored_mono (lane_anchored T.R.o (Equiv.refl _) (meshEquiv c) (radiusB x) S.patch.L.val S.patch.L.property V Pt.width.le ho) ha hd

lemma settles {S : StepData c f} {t : ℝ} (a : Directions G f) (h : ∀ i, ‖a i‖ ≤ t)
    (o r) (ht : 0 ≤ t) : settle S o r a ≤ chips S r*t := by
  unfold settle
  calc
    _ ≤ ∑ _∈members S o r,t := Finset.sum_le_sum (fun i _ => h i)
    _ = _ := by rw [Finset.sum_const,nsmul_eq_mul]
    _ ≤ chips S r*t := mul_le_mul_of_nonneg_right (saves ..) ht

/-- Coarse gauge in the rotated locations. Pick independently at each
use, no changing the orientation conventions or decisions of the matrix. -/
lemma coarseTrim (R : ℕ) (s : Signed) {A : Stores S} {V : Config G c} {o : Site c}
    {r : ℕ} (ho : s.act o ∉ A.dome r) (hr : R+1 ≤ r) (hp : 2*(R+1) < c.val) (h : A.flags=RG.flags (temp x) V) :
    let C := 16*(2*((R+1:ℕ):ℝ)+1)^5 * (Fintype.card PlaqAxes:ℝ)
    ∃ z : Site c → G.El,
      (∀ i : Bond c, separation o i.1 + 1 ≤ R → G.chord (Lattice.gauge z (pull s 0 V) i) ≤ C*temp x) ∧
      (∀ i : Bond f, separation o (S.ratio.parent i.1)+1 ≤ R →
        G.chord (Lattice.gauge (z ∘ S.ratio.parent) (facade S s V 0) i) ≤ C*temp x) := by
  intro C
  have hv (i : Site c) (hi : separation (s.act o) i ≤ r) (p : PlaqAxes) : toll V (i,p) ≤ temp x := by
    by_contra! hx
    have he : i∈ A.flags := h.symm ▸ (flags_spec ..).2 ⟨(i,p), by exact YM.Work.E01.base_touched (i,p), hx⟩
    exact ho (halo_spec.mpr ⟨i, Finset.mem_union_right _ he, (separation_comm ..).trans_le hi⟩)
  obtain ⟨w,hw⟩ := Work.E08.axial_patch (s.act o) V R (R+1) (by omega) hp (temp x) (temp_nonneg x) (fun i hi p => hv i (hi.trans hr) p)
  let z (x : Site c) := w (s.act x)
  refine ⟨z, fun i hi => ?_,fun i hi => ?_⟩
  · have hh : z=fun i => w (affine s (0:Site c) i) := funext fun i => by simp only [z,affine,add_zero]
    have ht : separation (s.act o) (sendEdge s 0 i).1 ≤ R := by
      unfold sendEdge affine Step.used; split
      · rename_i he
        change separation (s.act o) (s.act i.1+0-step (s.perm _)) ≤ R; rw [add_zero]
        have hv := Work.E03.sep_step ((s.act i.1)-step (s.perm i.2)) (s.perm i.2)
        rw [sub_add_cancel,separation_comm] at hv
        exact (separation_triangle _ (s.act i.1) _).trans ((Nat.add_le_add_left hv _).trans (by rwa [separation_signed]))
      · dsimp only; rw [add_zero,separation_signed]; omega
    rw [hh,← Work.F05.pull_gauge_zero,turn_read]; split
    · rw [G.chord_inv]; exact hw _ ht
    exact hw _ ht
  · have he : z ∘ S.ratio.parent = fun i => constantGauge w S.ratio (affine s (0:Site f) i) := by
      funext i; simp [z,constantGauge,affine,S.ratio.parent_signed S.patch.odd_side]
    have ht : separation (s.act o) (S.ratio.parent (sendEdge s 0 i).1) ≤ R := (spin_separation i s o).trans hi
    rw [fixed_facade,he,← Work.F05.pull_gauge_zero, copied _ S.patch.odd_side,turn_read]
    let j := sendEdge s (0:Site f) i
    have hv : G.chord (replica S.ratio (Lattice.gauge w V) j) ≤ C*temp x := by
      unfold replica; split
      · rw [G.chord_one]; unfold C; exact mul_nonneg (by positivity) (temp_nonneg _)
      exact hw _ ht
    split
    · rw [G.chord_inv]; exact hv
    exact hv

-- Scaled shell receipt, temperature convert globally next.
/-- Uniformly bound the base plaquette piece on selected rotated
stencils; $ell_R$ in a selected block may refer to p's where that p
block by itself was NOT selected: so give a spatial theorem rather than
requiring curb there. -/
lemma baseFace (G : Gauge) (P : Patch) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f)
      (A : Stores S) (V : Config G c) (s : Signed) (p : Cell f), S.patch=P → 100*(1+radiusB x) ≤ c.val →
        A.flags=RG.flags (temp x) V → s.act (S.ratio.parent p.1) ∉ A.dome (9*radiusB x) →
        ‖G.curvature (faceValue (facade S s V 0) p)‖ ≤ C*temp x := by
  open YM.SectorNext.Remainder.Affine in
    obtain ⟨C,r,hC,hr,H⟩ := face_affine G
    obtain ⟨L,t,hl,ht,H0⟩ := Next.Fluctuations.log_chart_cost G
    let X := permit P
    have hx : 0 < X := by unfold X permit; have h : Nonempty PlaqAxes := ⟨((⟨(0,1),by decide⟩):PlaqAxes)⟩; have hh : 0 < Fintype.card PlaqAxes := Fintype.card_pos; positivity
    let M := L*X
    have hm : 0 < M := mul_pos hl hx
    -- small costs spent by delay
    have Z (q δ : ℝ) (hδ : 0<δ) : ∀ᶠ x : ℝ in atTop, q*temp x ≤ δ := by
      filter_upwards [Work.E01.fiery_le G (1:Side) q,(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
      simpa [fiery,betaF] using hx.trans he
    refine ⟨C*M,mul_pos hC hm,?_⟩
    filter_upwards [Z X t ht,Z M r hr,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+2)] with x hv hy hR
    intro c f S A V s p hS hc hV hP
    obtain ⟨z,-,hz⟩ := coarseTrim (allot P) s hP (by omega) (by omega) hV
    let U := facade S s V 0
    let w := z ∘ S.ratio.parent
    let b (i : Bond f) := G.plog (G.mat (Lattice.gauge w U i))
    have hh (i : Fin 4) : G.chord (Lattice.gauge w U (patchFace p i)) ≤ X* temp x := hz _ (by
      have he := faceLink (S:=S) p i; unfold allot; omega)
    have hL (i) := H0 (Lattice.gauge w U (patchFace p i)) ((hh i).trans hv)
    have hb (i : Fin 4) : ‖b (patchFace p i)‖ ≤ M*temp x := by
      apply (hL i).2.trans; exact (mul_le_mul_of_nonneg_left (hh _) hl.le).trans_eq (mul_assoc L _ _).symm
    have hh : 0 ≤ M*temp x := mul_nonneg hm.le (temp_nonneg _)
    obtain ⟨-,-,hp,-⟩ := H f (increment U 0) U (0 : Directions G f) b p w (M*temp x) hh hy
      (fun _ => by rw [Pi.zero_apply,norm_zero]; exact hh) hb (fun _ => rfl) (fun i => (hL i).1.symm)
    exact hp.trans_eq (mul_assoc C M _).symm

lemma baseBond (G : Gauge) (P : Patch) (K : KernelChoices) (h : P.Branches K G) :
    ∃ C : ℝ, 0<C ∧ ∀ᶠ x : ℝ in atTop, ∀ {c f : Side} (S : StepData c f) (I : Forest S.ratio)
      (A : Stores S) (V : Config G c) (s : Signed) (i : Bond c) (k : S.Choices), S.patch=P → S.kernel=K → 100*(1+radiusB x) ≤ c.val →
        A.flags=RG.flags (temp x) V → curb (shots S x) A I x s (.inr i) →
        ‖Z S (S.prediction (facade S s V 0) (choice s k)) (pull s 0 V) i‖ ≤ C*temp x := by
  open YM.SectorNext.Remainder.Affine in
    obtain ⟨C,r,hC,hr,H⟩ := bond_local P K G h
    obtain ⟨L,t,hl,ht,H0⟩ := Next.Fluctuations.log_chart_cost G
    let X := permit P
    have hx : 0 < X := by unfold X permit; have h : Nonempty PlaqAxes := ⟨((⟨(0,1),by decide⟩):PlaqAxes)⟩; have hh : 0 < Fintype.card PlaqAxes := Fintype.card_pos; positivity
    let M := L*X
    have hm : 0 < M := mul_pos hl hx
    have Z' (q δ : ℝ) (hδ : 0<δ) : ∀ᶠ x : ℝ in atTop, q*temp x ≤ δ := by
      filter_upwards [Work.E01.fiery_le G (1:Side) q,(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
      simpa [fiery,betaF] using hx.trans he
    refine ⟨C*M,mul_pos hC hm,?_⟩
    filter_upwards [Z' X t ht,Z' M r hr,small_span P,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+2)] with x hv hy he hR
    intro c f S I A V s i k hS hK hc hV hI
    obtain ⟨z,hB,hU⟩ := coarseTrim (allot P) s (o:=i.1) ((guarded (hS.symm ▸ he) hI).1) (by omega) (by omega) hV
    let U := facade S s V 0
    let w := z ∘ S.ratio.parent
    let b (i : Bond f) := G.plog (G.mat (Lattice.gauge w U i))
    let B := G.plog (G.mat (Lattice.gauge z (pull s 0 V) i))
    have hh (j : Bond f) (hj : separation i.1 (S.ratio.parent j.1) ≤ predReach S.patch) : G.chord (Lattice.gauge w U j) ≤ X* temp x := hU _ (by rw [← hS]; unfold allot; omega)
    have hL (j) (hj : separation i.1 (S.ratio.parent (j:Bond f).1) ≤ predReach S.patch) := H0 (Lattice.gauge w U j) ((hh j hj).trans hv)
    have hb (j : Bond f) (hj : separation i.1 (S.ratio.parent j.1) ≤ predReach S.patch) : ‖b j‖ ≤ M*temp x := by
      apply (hL j hj).2.trans; exact (mul_le_mul_of_nonneg_left (hh _ hj) hl.le).trans_eq (mul_assoc L _ _).symm
    let q := Lattice.gauge z (pull s 0 V) i
    have hq : G.chord q ≤ X*temp x := hB _ (by rw [separation_self]; unfold allot; omega)
    have hZ := H0 q (hq.trans hv)
    have hB' : ‖B‖ ≤ M*temp x := (hZ.2.trans (mul_le_mul_of_nonneg_left hq hl.le)).trans_eq (mul_assoc L _ _).symm
    have hh : 0 ≤ M*temp x := mul_nonneg hm.le (temp_nonneg _)
    obtain ⟨-,-,-,-,hp,-⟩ := H c f S hS hK (increment U 0) U (pull s 0 V) 0 b B (choice s k) i z (M*temp x) hh hy
      (fun j hj => ⟨by rw [Pi.zero_apply,norm_zero]; exact hh,hb j hj⟩) hB' (fun _ _ => rfl) (fun j hj => (hL j hj).1.symm) hZ.1.symm
    exact hp.trans_eq (mul_assoc C M _).symm

lemma barrel_max (T : PathData G) {o : Clip} {σ C Λ : ℝ} (hT : T.Bounds o σ C Λ)
    (U : Config G f) (p : Cell f) (n : ℕ) (a : Cell f→G.Color) (t : ℝ) (ht : 0 ≤ t)
    (he : ∀ i, let l := (T.row p.2 i).2; l.length ≤ n → ‖a (Work.F03.slotFace l p.1)‖ ≤ t) :
    ‖barrel T n U a p‖ ≤ C*t := by
  let g i := T.row p.2 i; let w i := (g i).2
  let v (j : ℕ) : G.Color := if (w j).length ≤ n then (g j).1 • G.adjoint (travel U p.1 (w j).walk) (a (Work.F03.slotFace (w j) p.1)) else 0
  have hx : Summable v := barrel_summed T n _ _ p hT
  let q j := |(g j).1| *Real.exp (σ*(w j).length)
  have hQ : SumBudget q C := hT.rows p.2
  have hw j : ‖v j‖ ≤ q j*t := by
    unfold v; split
    next h =>
      rw [norm_smul,G.norm_adjoint,Real.norm_eq_abs]
      have h : |(g j).1| ≤ q j := le_mul_of_one_le_right (abs_nonneg _) (Real.one_le_exp (mul_nonneg hT.width.le (by positivity)))
      exact mul_le_mul h (he _ ‹_›) (norm_nonneg _) (hQ.1 _)
    rw [norm_zero]; exact mul_nonneg (hQ.1 _) ht
  change ‖∑' i, v i‖ ≤ _
  calc
    ‖_‖ ≤ ∑' i, ‖v i‖ := norm_tsum_le_tsum_norm hx.norm
    _ ≤ ∑' i, q i*t := hx.norm.tsum_le_tsum hw (hQ.2.1.mul_right _)
    _ ≤ _ := by rw [tsum_mul_right]; exact mul_le_mul_of_nonneg_right hQ.2.2 ht

set_option maxHeartbeats 600000 in
/-- F₀ regularized *source* (not b yet). Permit d choices bounded before x
by C_L times fiery. -/
lemma source (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G)
    (L : ℝ) (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
        ∀ (q : YM.Push.SectorMeasure.Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)),
          0 < d → d ≤ L*fiery G x P.L →
          ∀ i, |Rows.source T x V k (shots S x) A F q d Y i| ≤ C*fiery G x P.L := by
  obtain ⟨C0,r0,H0⟩ := baseFace G P
  obtain ⟨C1,r1,H1⟩ := baseBond G P Pt.bind h
  obtain ⟨D,rD,HD⟩ := caps G P.L Pt
  obtain ⟨u,δ,ru,hδ,Hu⟩ := earned P Pt.bind G h
  obtain ⟨M,hM,hg⟩ := face_global G
  let a := Pt.top.paths + Real.sqrt Pt.top.clip.direct
  let b := Real.sqrt Pt.bind.penalty
  have ha : 0 ≤ a := add_nonneg Pt.top.paths_pos.le (Real.sqrt_nonneg _)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  let n (r : ℕ) := (Fintype.card (Site P.L):ℝ)*(LocalJet.grain r*Fintype.card Axis)
  let k := n (predReach P)
  have hn (r : ℕ) : 0 ≤ n r := by unfold n LocalJet.grain; positivity
  let A := (a*(2*C0)+D)+(2*C1+D)
  let B := a*(M*(n 1*(2*L)))+b*(u*(k*(2*L)))
  have hA : 0 ≤ A := by unfold A; positivity
  have hB : 0 ≤ B := add_nonneg (mul_nonneg ha (mul_nonneg hM.le (mul_nonneg (hn _) (by positivity)))) (mul_nonneg hb (mul_nonneg ru.le (mul_nonneg (hn _) (by positivity))))
  refine ⟨slip*(A+B),mul_nonneg slip_pos.le (add_nonneg hA hB),?_⟩
  have H : ∀ᶠ x : ℝ in atTop, permit P*temp x ≤ δ := by
    filter_upwards [Work.E01.fiery_le G (1:Side) (permit P),(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
    simpa [fiery,betaF] using hx.trans he
  filter_upwards [H0,H1,HD,H,small_span P,Work.E04.eventually_temp_le _ (Work.E04.shift_nonneg G P.L),
    Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+120)] with x h0 h1 hD hU hw hφ hT
  intro c f S T hP hh hQ X F l V hr q d Y hd he i
  have hp : Authorized X V F x u := Hu S hP hQ.knobs F X V x hr hw (by omega) (by omega) hU
  have hprice (s : Signed) := hD S T (congr_arg Patch.L hP) hQ (pull s 0 V)
  let t := fiery G x P.L
  change d ≤ L*t at he
  have ht : 0 ≤ t := temp_nonneg _
  change temp x ≤ 2*t at hφ
  obtain ⟨v,cj,hA',-⟩ := hQ.feeds
  have hUp : T.up.Bounds T.high Pt.top.width Pt.top.paths v := by rw [hQ.high]; exact hA'
  let W := shots S x
  let z : Directions G f := input x X F (autoShell q d V Y)
  have hz (i : Bond f) : ‖z i‖ ≤ 2*d := by
    unfold z input; split
    · split
      · exact patched_small _ hd _
      · rw [norm_zero]; positivity
    rw [norm_zero]; positivity
  have hz' (s : Signed) (i : Bond f) : ‖inChannel s (replica S.ratio V) z i‖ ≤ 2*d := by rw [in_size]; exact hz _
  have hcost (s : Signed) (j : Cell f) : ‖plaquetteJet S V s j z‖ ≤ M * (n 1*(2*L*t)) := by
    rw [plaquetteJet,(plaquette_turn s V j (face_smooth _ _).contDiffAt).2]
    have hh : chips S 1=n 1 := by unfold chips n; rw [site_card,hP,site_card]
    refine (hg S j _ _).trans (mul_le_mul_of_nonneg_left ((settles _ (hz' s) _ _ (by positivity)).trans ?_) hM.le)
    rw [hh]
    apply mul_le_mul_of_nonneg_left _ (hn _); linarith
  obtain ⟨⟨s,j⟩,l0⟩ := i
  let p : Slots S := (s,j)
  have hv (u : LogArray G (Slots S)) : |tape.symm u (p,l0)| ≤ ‖u p‖ := by
    change |u p l0| ≤ _
    rw [← EuclideanSpace.basisFun_inner G.ColorIndex ℝ (u p) l0]; simpa using abs_real_inner_le_norm (EuclideanSpace.basisFun G.ColorIndex ℝ l0) (u p)
  apply (hv _).trans
  unfold Rows.restrict; split
  swap
  · rw [norm_zero]; have := slip_pos; exact mul_nonneg (mul_nonneg slip_pos.le (add_nonneg hA hB)) ht
  rename_i hi
  rw [norm_smul,Real.norm_of_nonneg slip_pos.le,mul_assoc slip,Pi.add_apply]
  apply mul_le_mul_of_nonneg_left _ slip_pos.le
  rw [add_mul]
  -- price active values from `keep`
  rcases j with j|j
  · let U := facade S s V 0
    change ‖faceFixed T x s V j+faceKick T x V z s j‖ ≤ A*t+B*t
    have hl : curb (shots S x) X F x s (.inl j.1) := hi
    let o := s.act (S.ratio.parent j.1.1)
    have h' : o ∉ X.dome (9*radiusB x+9*radiusB x/10) := (guarded (hP.symm ▸ hw) hl).1
    let D₀ (p : Cell f) := G.curvature (faceValue U p)
    have hF (p : Cell f) (h : separation o (s.act (S.ratio.parent p.1)) ≤ till x) : ‖D₀ p‖ ≤ 2*C0*t := by
      apply (h0 S X V s p hP hh hr (fun hp => h' ?_)).trans
      · nlinarith only [r0,hφ]
      obtain ⟨a,ha,he⟩ := halo_spec.mp hp
      unfold Stores.dome
      refine halo_spec.mpr ⟨a,ha,?_⟩
      have hv := separation_triangle a (s.act (S.ratio.parent p.1)) o
      rw [separation_comm o] at h; unfold Stores.till at h; omega
    have hH (p : Slot) (hp : p.length ≤ till x) : separation o (s.act (S.ratio.parent (Work.F03.slotFace p j.1.1).1)) ≤ till x := by
      unfold o; rw [separation_signed]; exact (slot_distance _ _).trans (by unfold Slot.length at hp; omega)
    apply (norm_add_le ..).trans
    apply add_le_add
    · unfold faceFixed
      apply (norm_sub_le ..).trans
      have hx : ‖T.Mv (till x) (temp x) (pull s 0 V) j‖ ≤ D*t := by
        apply ((hprice s).phi _).trans; rw [hP]; apply mul_le_mul_of_nonneg_right _ ht; exact div_le_self rD.le (one_le_pow₀ (Nat.one_le_cast.mpr P.L.property))
      have hw : ‖T.Xf (till x) U j‖ ≤ a*(2*C0*t) := by
        unfold Tube.Xf plotted; split
        · rw [← barrel_term]
          exact (barrel_max T.up hUp U j.1 (till x) D₀ _ (by positivity) (fun i hi => hF _ (hH _ hi))).trans
            (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _)) (by positivity))
        unfold shoot; rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hQ.high]
        exact mul_le_mul (le_add_of_nonneg_left Pt.top.paths_pos.le) (hF j.1 (by unfold o; simp)) (norm_nonneg _) ha
      change ‖T.Xf (till x) U j‖ + _ ≤ _
      unfold A; nlinarith only [hx,hw,mul_nonneg (show 0 ≤ 2*C1+D by positivity) ht]
    have hv := hcost s
    have hx (i : Cell f) : ‖plaquetteJet S V s i z‖ ≤ M*(n 1*(2*L*t)) := hv _
    have hLt : 0 ≤ 2*L*t := mul_nonneg (by positivity) ht
    have hh : 0 ≤ M*(n 1*(2*L*t)) := mul_nonneg hM.le (mul_nonneg (hn 1) hLt)
    apply le_trans (b:=a*(M*(n 1*(2*L*t))))
    · unfold faceKick; split
      · exact (barrel_max T.up hUp U j.1 (till x) (fun i => plaquetteJet S V s i z) _ hh (fun _ _ => hx _)).trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (Real.sqrt_nonneg _)) hh)
      rw [norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),hQ.high]
      exact mul_le_mul (le_add_of_nonneg_left Pt.top.paths_pos.le) (hx _) (norm_nonneg _) ha
    unfold B; have hh : 0 ≤ (b*(u*(k*(2*L))))*t := mul_nonneg (mul_nonneg hb (mul_nonneg ru.le (mul_nonneg (hn _) (by positivity)))) ht
    nlinarith only [hh]
  · change ‖noiseFixed x V l s j (T:=T)+noiseKick V l z s j‖ ≤ _
    apply (norm_add_le ..).trans
    change curb (shots S x) X F x s (.inr j) at hi
    apply add_le_add
    · unfold noiseFixed; apply (norm_sub_le ..).trans
      have hJ := h1 S F X V s j l hP hQ.knobs hh hr hi
      have hm := (hprice s).hot j; rw [hP] at hm
      change _ ≤ D*t at hm
      have hh : 0 ≤ a*(2*C0*t)+D*t := by positivity
      unfold A; nlinarith only [hJ,hm,mul_le_mul_of_nonneg_left hφ r1.le,hh]
    obtain ⟨-,hQ',hϕ⟩ := hp.noise s l j hi
    unfold noiseKick
    rw [norm_neg, norm_smul,Real.norm_of_nonneg (Real.sqrt_nonneg _),blockJet,(block_turn s V j l hQ').2,hQ.knobs]
    change b * _ ≤ _
    apply le_trans (b:=b*(u*(k*(2*L*t))))
    · apply mul_le_mul_of_nonneg_left _ hb
      apply (hϕ _).trans
      apply mul_le_mul_of_nonneg_left _ ru.le
      refine (settles _ (hz' s) _ _ (by positivity)).trans ?_
      rw [show chips S (predReach S.patch)=k by unfold chips k n; rw [site_card,hP,site_card]]
      exact mul_le_mul_of_nonneg_left (by linarith) (hn _)
    unfold B; have hh : 0≤(a*(M*(n 1*(2*L))))*t := mul_nonneg (mul_nonneg ha (mul_nonneg hM.le (mul_nonneg (hn _) (by positivity)))) ht
    nlinarith only [hh]

/-- Uniform fixed-L weak price on b itself at the d the change uses.
No y hypothesis, no period powers. -/
theorem real_price (G : Gauge) (P : Patch) (Pt : Teller G) (h : P.Branches Pt.bind G) (L : ℝ) (hL : 0≤L) :
    ∃ C : ℝ, 0≤C ∧ ∀ᶠ x : ℝ in atTop,
    ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → 100*(1+radiusB x) ≤ c.val → Pt.Funds S T →
      ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) (V : Config G c), A.flags=RG.flags (temp x) V →
        ∀ (q : YM.Push.SectorMeasure.Chi) (d : ℝ) (Y : LinkArray G (Frozen A x F)),
          0 < d → d ≤ L*fiery G x P.L →
          ∀ i, |Rows.blame T x V k (shots S x) A F q d Y i| ≤ C*fiery G x P.L := by
  obtain ⟨C,hC,H⟩ := source G P Pt h L hL
  obtain ⟨Q,δ,hQ,hδ,T0⟩ := written Pt.bind P G Pt h
  let σ := Pt.top.width/2
  have hs := Pt.top.width_pos
  have hσ : 0 < σ := half_pos hs
  let K (P : Patch) (s : ℝ) : ℝ :=
    Fintype.card G.ColorIndex * ((Fintype.card Signed:ℝ)*
    ((Fintype.card Bool * Fintype.card PlaqAxes * Fintype.card (Site P.L) * Tier.wealth s)+
      Fintype.card Axis * Tier.wealth s))
  let T (P : Patch) (s : ℝ) : ℝ :=
    ((Fintype.card G.ColorIndex : ℝ) * (Fintype.card (Site P.L) * Fintype.card Axis)) * Tier.wealth s
  let M := max (K P σ) (T P σ)*Q
  have hM : 0 ≤ M := by
    have he : 0 ≤ K P σ := by unfold K; have := Tier.wealth_nn σ; positivity
    exact mul_nonneg (he.trans (le_max_left ..)) hQ
  refine ⟨M*C,mul_nonneg hM hC,?_⟩
  have he : ∀ᶠ x : ℝ in atTop, permit P*temp x ≤ δ := by
    filter_upwards [Work.E01.fiery_le G (1:Side) (permit P),(Work.E01.largeT_tendsto G 1).eventually (ge_mem_nhds hδ)] with x hx he
    simpa [fiery,betaF] using hx.trans he
  filter_upwards [H,he,Work.E01.radiusB_tendsto.eventually_ge_atTop (allot P+20),small_span P] with x hx hφ hr hs'
  intro c f S U hP hp ht A F k V hV q d Y hd hw i
  have hh := T0 S U hP ht.knobs ht A V F x hV hs' (by omega) (by omega) hφ k
  have hA := Schur.pure hs hQ hh (Tier.down_price σ hσ S G) (Tier.front_price σ hσ A F G (x:=x))
  let B := Rows.move U x V k (shots S x) A F
  have hb : FreeResolvent.Cost.Schur (FreeResolvent.native c) (Wisps.down S) (front A F) 0 M B := by
    have hu := (pours_iff.mp hA).2.mono (show (0:ℝ) ≤ σ from hσ.le) le_rfl -- change equality
    have hg₁ : Tier.slotFee S G σ = K P σ := by
      unfold Tier.slotFee K; rw [site_card,hP,site_card]
    have hg₂ : Tier.keyFee S G σ = T P σ := by
      unfold Tier.keyFee T; rw [site_card,hP,site_card]
    unfold M; rw [← hg₁,← hg₂]; exact hu
  have hc j := hx S U hP hp ht A F k V hV q d Y hd hw j
  have hl := hb.cols.bound i
  simp only [FreeResolvent.Cost.weight_zero,one_mul] at hl
  let t := fiery G x P.L
  unfold blame mulVec dotProduct
  let b := Rows.source U x V k (shots S x) A F q d Y
  change |∑ j, B.transpose i j * b j| ≤ _
  calc
    _ ≤ ∑ j, |B.transpose i j| * (C*t) := (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun j _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc j) (abs_nonneg _))
    _ ≤ (M*C)*t := by rw [← Finset.sum_mul,mul_assoc]; exact mul_le_mul_of_nonneg_right hl (mul_nonneg hC (temp_nonneg _))
end SourceBill
end YM.AnalyticBridge.LocalGaussianLaws
