import YM.Planned.PRIMARY_INTEGRAL_295.Awheel
import YM.Planned.PRIMARY_INTEGRAL_295.Record
import YM.Work.F03.Flat




/-!
# Signed and color action on these SAME coefficient reels

Fields read on actual cover links, only eventually around the identity.
H.ToPart for the *full* coefficient/equivariance used for heading.
Rotation here is only a lattice symmetry, not the continuum quotient
O(4) claim. Includes translations of individual link origins implied by
flips. No claim about translation of placed physical cylinders /
reoptimizing histories across offsets.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Film
open Filter Function Set Lattice Labels RG Wilson Source Source.Drops Precision Bloch Next.Free Place Carrier
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {d j t : ℕ} {M : Side}

/-- Real linear changes of Snap data. Use `turnIn s` for link pulls by s,
matching the inverse motion in `Labels.tensor`. -/
def flipIn (G : Gauge) (d : ℕ) (f : (i : ℕ) → Module.End ℝ (Taylor G i)) : Snap G d →L[ℝ] Snap G d :=
    LinearMap.toContinuousLinearMap { toFun X i := f i.val (X i)
                                      map_add' _ _ := funext fun i=> map_add (f i.val) ..
                                      map_smul' _ _ := funext fun i=> map_smul (f i.val) .. }

def turnIn (G : Gauge) (d : ℕ) (s : Signed) := flipIn G d fun _=> Taylor.turn s.ortho⁻¹

def colorIn (G : Gauge) (d : ℕ) (u : G.El) := flipIn G d fun _=>Taylor.paint u

lemma expandTurn (f : (i : ℕ)→ Module.End ℝ (Taylor G i)) (X : Snap G d) : expand d (flipIn G d f X) = changedJet f (expand d X) := by
  funext i; by_cases h:i<d-1
  · rw [expand,dif_pos h,changedJet,expand,dif_pos h]; rfl
  simp only [expand,changedJet,dif_neg h,map_zero]

private lemma exp_adjoint (u : G.El) (x : G.Color) : G.lieExp (G.adjoint u x) = u * G.lieExp x * u⁻¹ := by
  apply G.mat_injective; simp only [G.mat_mul,G.mat_lieExp,G.mat_adjoint,G.exp_conjugate]; rfl

-- Preserve the actual law `H` as parameter supplied by primary constructor
lemma turn_pure (H : Hol G) (s : Signed) (X : Snap G d) : pureQuest H (turnIn G d s X) = pull s 0 (pureQuest H X) := by
  unfold pureQuest turnIn; rw [expandTurn, ← Work.G01.swirls_of_flow H s d]
lemma color_pure (H : Hol G) (u : G.El) (X : Snap G d) : pureQuest H (colorIn G d u X) = gauge (fun _=>u) (pureQuest H X) := by
  unfold pureQuest colorIn; rw [expandTurn,show changedJet _ (expand _ _) = colored u _ from rfl, Work.G01.links_colored]

def up (s : Signed) (i : Edge Cover) : Edge Cover := (goingUp s i.2 i.1,s.perm i.2)
lemma turn_site (s : Signed) (i : Edge Cover) (U : CoverConfig G) : pull s 0 U i = if s.flip i.2 then (U (up s i))⁻¹ else U (up s i) := by
  unfold pull up Step.read Step.used posDir Step.rotate; rw [going_spec]; cases ht:s.flip i.2 <;> simp [ht,delay,affine,sub_eq_add_neg]
lemma exp_bias (s : Signed) (i : Axis) (x : G.Color) : G.lieExp (bias s i • x) = if s.flip i then (G.lieExp x)⁻¹ else G.lieExp x := by
  unfold bias; split <;> simp [Work.F03.exp_neg_color]

lemma leak (H : Hol G) (i : Edge Cover) : ∀ᶠ X : Snap G d in 𝓝 0,
    G.lieExp (lane (seat i.1) i.2 X)=pureQuest H X i := by
  have he := Work.G02.linkGerm H d i
  have ht : Tendsto (fun X : Snap G d => pureQuest H X i) (𝓝 0) (𝓝 1) := by
    rw [← he.2.1]; exact ((G.continuous_mat.isClosedEmbedding G.mat_injective).isInducing.continuousAt_iff.mpr he.1.continuousAt).tendsto
  apply (ht.eventually G.plog_right).mono; intro x hx; rw [lane_truth H i]; exact hx

-- Snap change through stationary **predictions**. First the h-origin germs.
lemma shade (H : Hol G) (s : Signed) (i : Edge Cover) :
    (fun X : Snap G d=> lane (seat i.1) i.2 (turnIn G d s X)) =ᶠ[𝓝 0] fun X => bias s i.2 • lane (seat (up s i).1) (up s i).2 X := by
  let j:=up s i
  let v (X : Snap G d):=lane (seat j.1) j.2 X
  have he : Tendsto (fun X=> bias s i.2 • v X) (𝓝 0) (𝓝 0) := by
    have h : Tendsto v (𝓝 0) (𝓝 (v 0)) := (lane_smooth (G:=G) (d:=d) _ _).continuousAt.tendsto
    have hb := h.const_smul (bias s i.2)
    rwa [show v 0=0 from lane_root .., smul_zero] at hb
  filter_upwards [leak H (d:=d) j,he.eventually G.plog_left] with x hx hL
  rw [lane_truth H i,turn_pure,turn_site,← hx,← exp_bias]; exact hL

lemma light (H : Hol G) (u : G.El) (i : Edge Cover) :
    (fun X : Snap G d=> lane (seat i.1) i.2 (colorIn G d u X)) =ᶠ[𝓝 0] fun X => G.adjoint u (lane (seat i.1) i.2 X) := by
  let v (X:Snap G d):=lane (seat i.1) i.2 X
  have h : Tendsto v (𝓝 0) (𝓝 (v 0)) := (lane_smooth (G:=G) (d:=d) _ _).continuousAt.tendsto
  let g := (G.adjoint u).toContinuousLinearMap
  have hv := ((g.continuous.tendsto (v 0)).comp h)
  rw [show v 0=0 from lane_root ..,map_zero] at hv
  filter_upwards [leak H (d:=d) i,hv.eventually G.plog_left] with x hx hL
  rw [lane_truth H i,color_pure]; unfold Lattice.gauge; rw [← hx,← exp_adjoint]; exact hL

private lemma glide {b : Edge Cover} (e : Edge Cover) (J : Snap G d →L[ℝ] Snap G d) (K : G.Color →L[ℝ] G.Color) (X : Snap G d)
    (h : (fun X : Snap G d=>lane (seat b.1) b.2 (J X)) =ᶠ[𝓝 0] fun X=>K (lane (seat e.1) e.2 X)) :
    cut (J X) b.1 b.2=K (cut X e.1 e.2) := by
  let f (i : Edge Cover) (X : Snap G d) := lane (seat i.1) i.2 X
  have hf i : ContDiffAt ℝ d (f i) 0 := (lane_smooth ..).of_le le_top
  unfold cut Work.G05.blockTaylor; rw [Finset.sum_apply,Finset.sum_apply,map_sum]; refine Finset.sum_congr rfl fun n hn=> ?_
  have hk : n≤d := Nat.le_of_lt_succ (Finset.mem_range.mp hn)
  have he := (show (f b ∘ J) =ᶠ[𝓝 0] K ∘ f e from h).iteratedFDeriv ℝ n|>.eq_of_nhds
  rw [Next.Foundations.jets_linear J ((hf b).of_le (Nat.cast_le.mpr hk))] at he
  have heq := K.iteratedFDeriv_comp_left (hf e) (i:=n) (Nat.cast_le.mpr hk)
  change Tensor.diagonal (Tensor.coeff (f b) n 0) _=K (Tensor.diagonal (Tensor.coeff (f e) n 0) _)
  have hs : iteratedFDeriv ℝ n (f b) 0 (fun _=>J X)=K (iteratedFDeriv ℝ n (f e) 0 (fun _=>X)) := DFunLike.congr_fun (he.trans heq) (fun _ => X)
  simp [Tensor.diagonal,Tensor.coeff,hs]

lemma directed (H : Hol G) (s : Signed) (X : Snap G d) : cut (turnIn G d s X) = orient s (cut X) := by
  ext1 i; ext1 j
  exact glide (up s (i,j)) (turnIn G d s) (bias s j • ContinuousLinearMap.id ..) X (b:=(i,j)) (shade H s (i,j))
lemma guarded (H : Hol G) (u : G.El) (X : Snap G d) : cut (colorIn G d u X)=(fun x i=>G.adjoint u (cut X x i)) := by
  ext1 i; ext1 j
  exact glide (i,j) _ (G.adjoint u).toContinuousLinearMap X (b:=(i,j)) (light H u (i,j))

private def shell (A : Lines M) (X : Snap G d) : CoverConfig G := fun e=>G.lieExp (spool A X e.1 e.2)

lemma shells (H : Hol G) (s : Signed) (P : Flight j t) (k : ℝ) (hk : 0<k) (ht : 4≤t) (X : Snap G d) :
    shell (linesOf P k) (turnIn G d s X) = pull s 0 (shell (linesOf P k) X) := by
  ext1 i; rw [turn_site]; unfold shell spool; rw [directed H s X,origin_turn s P k hk ht]; exact exp_bias ..
lemma returns (H : Hol G) (u : G.El) {A : Lines M} (h : Whole A) (X : Snap G d) :
    shell A (colorIn G d u X) = gauge (fun _=>u) (shell A X) := by
  funext i
  obtain ⟨C,hC⟩ := cut_paid X
  have hx := echo_linear h (G.adjoint u).toContinuousLinearMap hC
  unfold shell Lattice.gauge spool
  rw [guarded H u X,show applyLine A (fun x i=>G.adjoint u (cut X x i))=fun x i=>G.adjoint u (applyLine A (cut X) x i) from hx]; exact exp_adjoint ..

variable {F : Labels.Frame G d} (T : SectionData F) (v : F.Coeff) (H : Hol G) (h : T.Sound H)
private lemma surface (X : Snap G d) (A : Lines M) : slant T v (trace T.stencil A X)=T.evaluate v (shell A X) := by
  unfold slant; apply T.cylinder_local; intro p h1 h2; exact pore_site _ (S:=T.stencil) ⟨(⟨p.1,h1⟩,p.2),h2⟩
include h

theorem swirl (s : Signed) (P : Flight j t) (k : ℝ) (hk : 0<k) (ht : 4≤t) (X : Snap G d) :
    let f := trace T.stencil (linesOf P k)
    slant T v (f (turnIn G d s X))=slant T (F.act s.ortho v) (f X) := by
  intro a; unfold a; rw [surface,shells H s P k hk ht,h.Hpart,surface]

theorem mapped_color {A : Lines M} (hh : Whole A) (u : G.El) (X : Snap G d) :
    let f := trace T.stencil A
    slant T v (f (colorIn G d u X))=slant T v (f X) := by
  intro a; unfold a; rw [surface,returns H u hh,h.gaugeInvariant,surface]
end YM.Planned.PrimaryIntegral295.Film
