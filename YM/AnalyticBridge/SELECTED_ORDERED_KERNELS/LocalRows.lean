import YM.AnalyticBridge.SELECTED_ORDERED_KERNELS.Vicinity

/-!
# Period-uniform coefficients at a nonzero no-hole log background B

Finite row stencils first. `around` means *ordinary additive translation*
of existing exponential coordinate functions, NOT translation by the group
when taking derivatives. Only used to build input to off-centre conversion.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SelectedOrderedKernels.Small
open Lattice Wilson RG Precision Tree Exterior Function Filter Topology Bloch Laurent Metric FreeResolvent Affine
  Lifted View TestD Mark
open scoped BigOperators Topology Matrix.Norms.Frobenius ContDiff

variable {G : Gauge} {c f : Side} {P : Patch} {K : KernelChoices} {h : f.val=c.val*P.L.val} {R n : ℕ}

section translation
variable {X E τ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup X] [NormedSpace ℝ X]

def around (x : X) (F : X → E) (y : X) := F (y+x)

lemma slide (x : X) (F : X → E) (n : ℕ∞ω) : ContDiffAt ℝ n (around x F) 0 ↔ ContDiffAt ℝ n F x := by
  constructor
  · intro h
    rw [show F = (around x F) ∘ (fun y => y-x) from by ext y; simp [around]]
    apply (show ContDiffAt ℝ n (around x F) (x-x) from (sub_self x).symm ▸ h).comp (f:=fun y => y-x) x (contDiffAt_id.sub contDiffAt_const)
  intro h
  apply ContDiffAt.comp (g:=F) (f:=fun y => y+x) _ _ (contDiffAt_id.add contDiffAt_const)
  simpa

lemma jet_translate (x : X) (F : X → E) (v : τ → X) (l : List τ) : jet v (around x F) l 0 = jet v F l x := by
  unfold around; rw [jet,iteratedFDeriv_comp_add_right,zero_add]; rfl
end translation



def UniformWatch (P : Patch) (G : Gauge) (K : KernelChoices) (r : ℝ) : Prop :=
    ∀ {c f : Side} {h : f.val=c.val*P.L.val}, 1<c.val → ∀ k : (data h K).Choices, ∀ y : pair G c f, ‖y‖ < r → Watch (data h K) k y
namespace UniformWatch
variable {r : ℝ} (hw : UniformWatch P G K r) (hc : 1<c.val) (t : (data h K).Choices) {x : pair G c f}
include hw hc t

lemma paid (hy : ‖x‖ < r) : ∀ᶠ z in 𝓝 x, Watch (data h K) t z ∧ Watch (data h K) t (G:=G) (z.1,0) := by
  filter_upwards [(isOpen_ball (α:=pair G c f)).mem_nhds (mem_ball_zero_iff.mpr hy)] with z hz
  rw [mem_ball_zero_iff] at hz; refine ⟨hw hc t z hz,hw hc t (z.1,0) ?_⟩
  rw [Prod.norm_def,norm_zero,max_eq_left (norm_nonneg _)]; exact (norm_fst_le z).trans_lt hz


end UniformWatch

-- one cost C for both fixed k derivative families before localization weights (post-L)
lemma vicinity_cost (P : Patch) (G : Gauge) (K : KernelChoices) (hb : P.Branches K G) (n : ℕ) : ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
    UniformWatch P G K r ∧
    ∀ {c f : Side} {h : f.val=c.val*P.L.val}, 1<c.val → ∀ (s : Signed) (t : (data h K).Choices) (x : pair G c f), ‖x‖ < r →
    let S := data h K
    (ContDiffAt ℝ ω (faces S s) x ∧ ∀ (i : tile G f) (j : ℕ), j ≤ n → ‖iteratedFDeriv ℝ j (fun z => faces S s z i) x‖ ≤ C) ∧
    (ContDiffAt ℝ ω (gaugeQ S s t) x ∧ ∀ (i : raw G c) (j : ℕ), j ≤ n → ‖iteratedFDeriv ℝ j (fun z => gaugeQ S s t z i) x‖ ≤ C) := by
  let R := reach P+2
  let U := refStep P K 4; let V := refStep P K R; let u := Classical.arbitrary V.Choices
  obtain ⟨r0,hr0,h0⟩ := holdWatch P G K hb
  change UniformWatch P G K r0 at h0
  obtain ⟨r1,C,hr1,hC,h1⟩ := local_costs (faces U (G:=G)) n fun i => (face_smooth _).contDiffAt
  obtain ⟨r2,D,hr2,hD,h2⟩ := local_costs (fun i => gaugeQ V i u (G:=G)) n fun i => duct_smooth hb i _
  refine ⟨min r0 (min r1 r2),max C D,lt_min hr0 (lt_min hr1 hr2),(hC.trans_le (le_max_left ..)).le,
    fun hy k p hx => h0 hy k p (hx.trans_le (min_le_left ..)),?_⟩
  intro c f h hc s t x hx S
  have hx1 := hx.trans_le ((min_le_right ..).trans (min_le_left r1 r2))
  have hx2 := hx.trans_le ((min_le_right ..).trans (min_le_right r1 r2))
  have hA (r) : 1 < (area r).val := by change 1<2*r+2; omega
  constructor
  · refine ⟨(face_smooth s).contDiffAt,fun i j hj => ?_⟩
    obtain ⟨w,hw⟩ := tile_root S s i
    let L := sheet G 4 h K (named S s i)
    have he : (fun z => faces S s z i)=ᶠ[𝓝 x] fun z => faces U s (L z) (fineHere U s (0:Site (area 4)) 0 w) :=
      Eventually.of_forall fun z => (congr_arg (faces S s z) hw).trans ((transported 4 _ z).plaquettes hc (hA _) s 0 w (by simp [size]))
    exact ((transferred _ L (transported_size ..) h1 s _ x hx1 he).2 j hj).trans (le_max_left ..)
  have hh (i : raw G c) : ContDiffAt ℝ ω (fun z => gaugeQ S s t z i) x ∧ ∀ j ≤ n, ‖iteratedFDeriv ℝ j (fun z => gaugeQ S s t z i) x‖ ≤ D := by
    let L := sheet G R h K (namedCo s i)
    have ht : ‖x‖ < r0 := hx.trans_le (min_le_left ..)
    have hL : ‖L x‖ < r0 := ((L.le_opNorm _).trans (mul_le_of_le_one_left (norm_nonneg _) (transported_size ..))).trans_lt ht
    have hview : (fun z => gaugeQ S s t z i) =ᶠ[𝓝 x] fun z => gaugeQ V s u (L z) (coarseHere s (0:Site (area R)) 0 i.2) := by
      filter_upwards [h0.paid hc t ht,(L.continuous.tendsto _).eventually (h0.paid (hA _) u hL)] with z ha hb'
      have he := responseView hc (hA _) s 0 i.2 hb (transported R (namedCo s i) z (h:=h)) (by simp [size,R]) ha.1 hb'.1 ha.2 hb'.2
      rw [← View.ring_root s i] at he; exact he
    exact transferred (fun s => gaugeQ V s u) L (transported_size ..) h2 _ _ _ hx2 hview
  exact ⟨contDiffAt_pi.mpr (fun i => (hh i).1),fun i j hj => ((hh i).2 j hj).trans (le_max_right ..)⟩

section budgets
variable {A γ d V r : ℝ}



def faceFoot (P : Patch) (G : Gauge) (γ : ℝ) (n : ℕ) (C : ℝ) := altitude
  (max (torusPay (Co P.L (PAC G 1)) γ) (torusPay (Co P.L (PAC G 2)) γ)) γ n 4 C

def noiseFoot (P : Patch) (G : Gauge) (γ : ℝ) (n : ℕ) (C : ℝ) := altitude
  (max (torusPay (Co P.L (PAC G 1)) γ) (torusPay (PAC G 1) γ)) γ n (reach P+2) C

lemma foot_nn (P : Patch) (G : Gauge) (h : 0 < γ) (n : ℕ) (hA : 0 ≤ A) :
    0 ≤ faceFoot P G γ n A ∧ 0 ≤ noiseFoot P G γ n A := ⟨altitude_nn (le_max_of_le_right (torusPay_nn _ _ h)) hA,
      altitude_nn (le_max_of_le_right (torusPay_nn _ _ h)) hA⟩


end budgets
end YM.SelectedOrderedKernels.Small
