import YM.Extra.ITERATION_NO_LOSS.Channel
import YM.Extra.ITERATION_NO_LOSS.Jets
import YM.Extra.ITERATION_NO_LOSS.Patterns
import YM.Next.FOUNDATIONS.SU2
import YM.Work.F02
import YM.Work.F03


/-!
# Match the inherited leading degree, on unmasked stationary actions
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration
open Filter Function Lattice Wilson RG Exterior Precision Tree Bloch Bid
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {n c f : Side} {k : ℕ} {ι : Type*}

def action (A : ℕ → Atom G k) (U : Config G n) := Patch.average fun s : Signed => uncut A (pull s 0 U)

lemma action_join {A B : ℕ → Atom G k} {σ C D : ℝ} (hs : 0 < σ) (ha : Charged A σ C) (hb : Charged B σ D) (U : Config G n) :
    action (join A B) U = action A U + action B U := by
  have he (V : Config G n) (x : Site n) :
      (∑' i, ((join A B) i).unmasked V x) = (∑' i, (A i).unmasked V x) + ∑' i, (B i).unmasked V x := by
    let f (i : ℕ ⊕ ℕ) := (Sum.elim A B i).unmasked V x
    have h (M : ℕ → Atom G k) {a : ℝ} (hm : Charged M σ a) : Summable (fun i => (M i).unmasked V x) :=
      .of_norm_bounded ((hm.absolute hs.le).mul_right _) (fun i => (M i).unmasked_bound ..)
    calc
      _ = ∑' i, f i := (numbering _).tsum_eq _
      _ = _ := Summable.tsum_sum (f:=f) (h _ ha) (h _ hb)
  simp only [action,uncut,Patch.average,he,Finset.sum_add_distrib,mul_add]

lemma action_smooth {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {x : X} {V : X → Config G n}
    {A : ℕ → Atom G k} {σ C : ℝ} (hs : 0 < σ) (ha : Charged A σ C) (hV : ∀ i,ContDiffAt ℝ ω (fun y => G.mat (V y i)) x) :
    ContDiffAt ℝ ω (fun y => action A (V y)) x := by
  refine ContDiffAt.mul (contDiffAt_const (c:=_)) (ContDiffAt.sum (f:=fun s z => uncut A (pull s 0 (V z))) fun s _ => ?_)
  refine Work.F02.uncut_contDiffAt hs ha fun i => ?_
  unfold pull Step.read; split
  · exact (show G.Mat ≃L[ℝ] G.Mat from starL ℝ).contDiff.contDiffAt.comp x (hV _)
  exact hV _

lemma action_limit (M : ℕ → Atom G k) {σ C : ℝ} (hs : 0 < σ) (ha : Charged M σ C) (v : Dir G n) :
    Tendsto (fun t : ℝ => action M (represent (t • v)) / t^k) (𝓝[≠] 0)
    (𝓝 (Patch.average fun s : Signed => total (plain ∘ M) (flux (pulled v s)))) := by
  simp_rw [action,Patch.average, Work.F03.represent_pulled, mul_div_assoc, Finset.sum_div, comp_def plain,
    total_flux _ _ hs.le ha]; exact Tendsto.const_mul _ (tendsto_finsetSum _ fun _ _ => Work.F03.atoms_limit _ _ hs ha)

lemma lower_jet {M : ℕ → Atom G k} {σ C : ℝ} (hs : 0 < σ) (hm : Charged M σ C) (i) (hi : i < k) :
    iteratedFDeriv ℝ i (action M (n:=n) ∘ represent) 0 = 0 :=
  Jets.negligible (action_smooth hs hm (fun _ => Work.F03.represent_smooth .. |>.contDiffAt) |>.of_le le_top)
    (fun v => Jets.drop hi (action_limit M hs hm v)) i le_rfl

section trajectory
variable {S : StepData c f} {H : Forest S.ratio} (ρ : Dir G c → AxisChart G H)

def liftedTo (H : Forest S.ratio) (ρ : Dir G c → AxisChart G H) (x : Dir G c) := lifting H (represent x) (ρ x)

def chartOf (H : Forest S.ratio) (ρ : Dir G c → AxisChart G H) (x : Dir G c) := Work.F03.axisLog H (x,ρ x)

lemma graph_jet (hr : ContDiffAt ℝ ω ρ 0) : ContDiffAt ℝ ω (fun x : Dir G c => (x,ρ x)) 0 := contDiffAt_id.prodMk hr
lemma chart_jet (hr : ContDiffAt ℝ ω ρ 0) (hz : ρ 0=0) : ContDiffAt ℝ ω (chartOf H ρ) 0 := by
  have he := Work.F03.inclusion_smooth (G:=G) H |>.snd
  rw [show (0 : Work.F03.ChartVars H G) = ((0 : Dir G c),ρ 0) by rw [hz]; rfl] at he
  exact he.comp (f:=fun x => (x,ρ x)) 0 (graph_jet ρ hr)
lemma liftedTo_smooth (hr : ContDiffAt ℝ ω ρ 0) (hz : ρ 0 = 0) (e) : ContDiffAt ℝ ω (fun x => G.mat (liftedTo H ρ x e)) 0 := by
  have he := Work.F03.live_smooth (G:=G) H e
  rw [show (0 : Work.F03.ChartVars H G) = ((0 : Dir G c),ρ 0) by rw [hz]; rfl] at he
  exact he.comp (f:=fun x => (x,ρ x)) 0 (graph_jet ρ hr)
lemma chart_tangent {W : PathData G} {p : Clip} {U : Matrix (Body 1 f) (Body 1 c) ℝ} (h : Critical H p W ρ)
    (hg : Guessed H U ρ) (x : Dir G c) : fderiv ℝ (chartOf H ρ) 0 x = Channel.rising H U x := by
  have hf := Work.F03.inclusion_smooth (G:=G) H
  let w (x : Dir G c) := (x,ρ x)
  have hz : w 0 = 0 := by unfold w; rw [h.1]; rfl
  have he : HasFDerivAt w _ 0 := hasFDerivAt_id _ |>.prodMk (h.2.1.differentiableAt (by simp)).hasFDerivAt
  have hy := (((hz.symm ▸ (hf.differentiableAt (by simp)).hasFDerivAt : HasFDerivAt _ _ (w 0)).comp 0 he).snd).fderiv
  change fderiv ℝ (chartOf H ρ) 0 = _ at hy
  have hr : fderiv ℝ ρ 0 x = relative H U x := (Push.side ρ (h.2.1.differentiableAt (by simp)) x).unique (hg x)
  rw [hy]
  change (fderiv ℝ (Work.F03.inclusion H) _ (x, fderiv ℝ ρ 0 x)).2 = _
  rw [show w 0 = 0 from hz, hr, Work.F03.inclusion_deriv]; rfl

lemma transmit {A B : ℕ → Atom G k} {W : PathData G} {p : Clip} {U : Matrix (Body 1 f) (Body 1 c) ℝ}
    {η σ C D : ℝ} (hη : 0 < η) (hσ : 0 < σ) (ha : Charged A η C) (hb : Charged B σ D) (hr : Critical H p W ρ) (hq : Guessed H U ρ)
    (ht : ∀ v s, total (plain ∘ A) (flux (pulled (Channel.rising H U v) s)) = total (plain ∘ B) (flux (pulled v s))) :
    ∀ j ≤ k, SameJet j (fun x => action A (liftedTo H ρ x)) (fun x => action B (represent x)) := by
  let a := action A (n:=f) ∘ represent
  let b := action B (n:=c) ∘ represent
  let g := chartOf H ρ
  let L := fderiv ℝ g 0
  have h0 : g 0 = 0 := by unfold g chartOf; rw [hr.1]; exact congr_arg Prod.snd (Work.F03.inclusion_zero (G:=G) H)
  have he := action_smooth (n:=f) hη ha (x:=0) (fun i => (Work.F03.represent_smooth i).contDiffAt)
  have he' := action_smooth (n:=c) hσ hb (x:=0) (fun i => (Work.F03.represent_smooth i).contDiffAt)
  have hG : ContDiffAt ℝ ω g 0 := chart_jet ρ hr.2.1 hr.1
  have ht' := Jets.tangent (f:=a) (d:=k) (he.of_le le_top) (hG.of_le le_top) h0 (lower_jet hη ha)
  have hg : a ∘ g =ᶠ[𝓝 0] fun x => action A (liftedTo H ρ x) := by
    have hq := (graph_jet ρ hr.2.1).continuousAt.tendsto
    rw [show ((0 : Dir G c),ρ 0) = 0 by rw [hr.1]; rfl] at hq
    filter_upwards [hq.eventually (Work.F03.inclusion_works (G:=G) H)] with x hx
    exact congr_arg (action A) hx
  have hL : ContDiffAt ℝ ω (a ∘ L) 0 := (L.map_zero.symm ▸ he).comp 0 L.contDiff.contDiffAt
  have hM := Jets.leading (d:=k) hL (g:=b) he' (fun x => ?_) (action_limit B hσ hb)
  · intro j hj
    exact ⟨action_smooth hη ha (liftedTo_smooth ρ hr.2.1 hr.1),he', (hg.symm.iteratedFDeriv ℝ _ |>.self_of_nhds).trans
      ((ht' j hj).trans (hM j hj).2.2)⟩
  have h := action_limit A hη ha (L x)
  rw [show L x = _ from chart_tangent ρ hr hq x] at h
  simp only [ht] at h
  simpa only [a,Function.comp_apply, L.map_smul, show L x = _ from chart_tangent ρ hr hq x] using h
end trajectory
end YM.Extra.Iteration
