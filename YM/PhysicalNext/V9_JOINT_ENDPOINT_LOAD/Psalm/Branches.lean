import YM.Extra.MULTISOURCE_BOUNDS.Step
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Sonata
import YM.ProofPorts.COMMON_COMPLEX_PRODUCTION.Pool



/-! # Predictor branch queries in central guards at *actual* θ on the
requested integrating stencils. Account for wrap and paths for both
frames; only temporary gauge transport of same prediction operations. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Psalm
open Function Filter Set Lattice Wilson RG Tree Pressure Precision Next Next.SectorChange Wisps Bid
   Push.SectorMeasure WardBin.Lies Push.GridApprox AnalyticBridge.LocalGaussian
open scoped Topology BigOperators Matrix.Norms.Frobenius Classical ContDiff
variable {G : Gauge} {c f : Side} {S : StepData c f} {k : S.Choices} {u t : ℝ} {V W : Config G c} {U U' : Config G f}
    {e : Bond c} {g : Site c → G.El}

abbrev uses (S : StepData c f) (x : Site c) (U : Config G f) := S.patch.usesMin S.kernel (expandAt (S.ratio.embed x) U)
abbrev taps (_S : StepData c f) (e : Bond c) := pinPos e

structure Conduct (S : StepData c f) (k : S.Choices) (U : Config G f) (V : Config G c) (i : Bond c) (t : ℝ) : Prop where
  frames (x) : x ∈ taps S i → uses S x U
  branch : S.patch.usesBest S.kernel (S.connector U k.1 i)
  sound : wire (S.prediction U k) V i < t

-- also keep one-site query about frame likelihood when THAT only is a read
private lemma visits_cover {r : ℕ} (w : Walk) {x : Cover} (h : x∈box r) (y : Cover) (hy : y∈visits x w) : y∈box (r+w.length) := by
  induction w generalizing r x with
  | nil => rcases List.mem_singleton.mp hy with rfl; exact h
  | cons d w ih =>
    rcases List.mem_cons.mp hy with hx|hx
    · subst y; exact box_larger h (Nat.le_add_right ..)
    have ht : x+d.vec ∈ box (r+1) := by
      rw [box_test] at *
      have hh (i) : -((r+1:ℕ):ℤ) ≤ (x+d.vec : Cover) i ∧ (x+d.vec:Cover) i ≤ ↑(r+1:ℕ) := by
        have h1 := h.1 i; have h2 := h.2 i
        rcases d with ⟨j,_|_⟩ <;> by_cases he : i=j <;> simp [Step.vec,he] at h1 h2 ⊢ <;> omega
      exact ⟨fun i => (hh i).1,fun i => (hh i).2⟩
    exact box_larger (ih ht hx) (by simp; omega)

private lemma expand_match {x : Site f} {r : ℕ} (h : Agrees (Push.GridApprox.window x r) U U') :
    Agrees (↑(box r) : Set Cover) (expandAt x U) (expandAt x U') := by
  rintro ⟨p,i⟩ hp hi; exact h (wrap f p+x,i) ⟨p,hp,rfl⟩ ⟨p+step i,hi,by simp [add_right_comm]⟩
lemma uses_same (S : StepData c f) (x : Site c) (hu : Agrees (frameUses S x) U U') : uses S x U ↔ uses S x U' := by
  have he (i j : S.patch.Points) (l : Lattice.Order) : travel (expandAt (S.ratio.embed x) U) i.val (route i.val j.val l) = travel (expandAt (S.ratio.embed x) U') i.val (route i.val j.val l) := by
    have he p (hp : p∈visits i.val (route i.val j.val l)) := visits_cover _ i.property p hp
    have hd := Push.Uniform.routeLe S.patch i j l
    have hl : S.patch.radius + (route i.val j.val l).length ≤ Push.GridApprox.reach S.patch := by unfold Push.GridApprox.reach; omega
    exact travel_local i.val (route i.val j.val l) _ _ (fun p h h' => expand_match hu p (box_larger (he _ h) hl) (box_larger (he _ h') hl))
  simp only [uses, Patch.usesMin, Patch.via,Patch.axial,he]

lemma taps_first (e : Bond c) : e.1∈taps S e := by simp [taps,pinPos]
lemma taps_last (e : Bond c) : e.1+step e.2∈taps S e := by simp [taps,pinPos]
lemma within_predictor {y : Site c} (h : y∈taps S e) : frameUses S y ⊆ predictorUses S e := by
  rcases Finset.mem_insert.mp h with rfl|h
  · exact subset_union_left
  cases Finset.mem_singleton.mp h; exact subset_union_right

variable (hS : S.patch.Branches S.kernel G)
include hS
lemma Conduct.read (h : Conduct S k U V e t) (hu : Agrees (predictorUses S e) U U') : Conduct S k U' V e t := by
  have hy y (hy : y∈taps S e) : Agrees (frameUses S y) U U' := fun i hi hj => hu i (within_predictor hy hi) (within_predictor hy hj)
  have hc := connector_dep S hS e k.1 k.1 rfl rfl (hy _ (taps_first ..)) (hy _ (taps_last ..))
  refine ⟨fun y hi => (uses_same S y (hy y hi)).mp (h.frames y hi),hc ▸ h.branch,?_⟩
  unfold wire StepData.prediction; rw [← hc]; exact h.sound

omit hS in
lemma uses_gauged (S : StepData c f) (g : Site f→ G.El) (x : Site c) : uses S x (gauge g U) ↔ uses S x U := by
  rw [uses,expandAt_gauge]; exact Patch.min_gauged ..
lemma Conduct.ungauge (h : Conduct S k (gauge (g ∘ S.ratio.parent) U) (Lattice.gauge g V) e t) : Conduct S k U V e t := by
  obtain ⟨h1,h2,h3⟩ := h
  have he := S.updateGauged hS (g ∘ S.ratio.parent) U k.1 e; simp only [Function.comp_apply,Ratio.embed_parent] at he
  have hg u : S.patch.bondCost (S.connector (gauge (g ∘ S.ratio.parent) U) k.1 e) (g e.1*u*(g (e.1+step e.2))⁻¹)= S.patch.bondCost (S.connector U k.1 e) u := by
    rw [he]; exact Finset.sum_congr rfl fun i _ => congr_arg (_ * ·) ((congr_arg G.price (by group : g e.1 * _ * (g (e.1+step e.2))⁻¹ * (g e.1*u*(g (e.1+step e.2))⁻¹)⁻¹=g e.1*(S.connector U k.1 e i*u⁻¹)*(g e.1)⁻¹)).trans (G.price_conj ..))
  refine ⟨fun x hx => (uses_gauged ..).mp (h1 x hx),?_,?_⟩
  · let Y := S.patch.best (S.connector (gauge (g ∘ S.ratio.parent) U) k.1 e)
    let y := (g e.1)⁻¹*Y*(g (e.1+step e.2))
    change S.patch.bondCost _ Y < _ at h2
    rw [← show g e.1*y*(g (e.1+step e.2))⁻¹=Y by unfold y; group, hg] at h2
    exact ((S.patch.bond_min _).choose_spec y).trans_lt h2
  have hx : S.prediction (gauge (g ∘ S.ratio.parent) U) k e=g e.1*S.prediction U k e*(g (e.1+step e.2))⁻¹ := by
    rw [StepData.prediction,he]; exact (S.patch.bond_gauge (h:=hS) ..).2
  rw [wire,hx,Lattice.gauge, show g e.1 * V e * (g (e.1+step e.2))⁻¹ * _⁻¹= g e.1*(V e*(S.prediction U k e)⁻¹)*(g e.1)⁻¹ by group, G.chord_conj] at h3
  exact h3

omit hS in
lemma uses_open (i : Site c) (h : uses S i U) : ∀ᶠ u in 𝓝 U, uses S i u := (show Continuous (expandAt (K:=G.El) (S.ratio.embed i)) by unfold expandAt; fun_prop).continuousAt.eventually
    (S.patch.min_open.mem_nhds h)

lemma Conduct.opened (h : Conduct S k U V e t) : ∀ᶠ p : Config G f × Config G c in 𝓝 (U,V), Conduct S k p.1 p.2 e t := by
  have hu := eventually_all.mpr (fun i : ↥(taps S e) => uses_open i.val (h.frames _ i.property))
  have hv i (hi : i∈taps S e) : ContinuousAt (fun U : Config G f => S.frames U k.1 i) U := by
    have hh := h.frames i hi
    let Q := expandAt (K:=G.El) (S.ratio.embed i)
    have hg := ((S.patch.selected_cont hS).continuousAt (S.patch.min_open.mem_nhds hh)).comp (x:=U) ((show Continuous Q by unfold Q expandAt; fun_prop).continuousAt)
    exact ContinuousAt.congr_of_eventuallyEq (f:=S.patch.selected ∘ Q) hg ((uses_open i hh).mono fun u h => if_pos h)
  have hc : ContinuousAt (fun p : Config G f × Config G c => S.connector p.1 k.1 e) (U,V) := by
    refine continuousAt_pi.mpr (fun i => ?_)
    unfold StepData.connector
    refine (((continuous_apply i).continuousAt.comp ((hv _ (taps_first e)).comp (continuousAt_fst (p:=(U,V))))).mul ?_).mul ((continuous_apply i).continuousAt.comp ((hv _ (taps_last e)).comp (continuousAt_fst (p:=(U,V))))).inv
    exact (show Continuous (fun p : Config G f × Config G c => travel (expandAt (S.ratio.embed e.1) p.1) i.val (List.replicate S.patch.L.val (posDir e.2))) from (continuous_travel ..).comp (by unfold expandAt; fun_prop)).continuousAt
  have ht := S.patch.best_open.mem_nhds h.branch
  have hP := (S.patch.best_cont hS).continuousAt ht
  have hf : ContinuousAt (fun p : Config G f × Config G c => wire (S.prediction p.1 k) p.2 e) (U,V) := by
    refine (show Continuous G.chord by fun_prop).continuousAt.comp (((continuous_apply e).continuousAt.comp (continuousAt_snd (p:=(U,V)))).mul (ContinuousAt.inv ?_))
    exact ContinuousAt.congr_of_eventuallyEq (hP.comp (f:=fun p : Config G f × Config G c => S.connector p.1 k.1 e) (x:=(U,V)) hc) ((hc.eventually ht).mono (fun p hp => if_pos hp))
  filter_upwards [(continuousAt_fst (p:=(U,V))).eventually hu, hc.eventually ht, hf.eventually (gt_mem_nhds h.sound)] with p ht h f
  exact ⟨fun i hi => ht ⟨i,hi⟩,h,f⟩
end YM.PhysicalNext.JointLoad.Psalm
