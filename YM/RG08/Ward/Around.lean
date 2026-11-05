import YM.RG08.Ward.Brocade
/-!
# Finite-period symmetry for this step with its Wick LOG connected stencils,
universal truncation. `Excise` only for normalized action. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} {G : Gauge} {F : Air G} (P : Patch) (k : KernelChoices) (X : Repeated P.L)
variable (w : Train P.J) (i : G.ColorIndex) (D : ChartRatio G) (hd : LocalRatio D)

abbrev veil (q : Option Side) (F : Air G) := exhale (conditionalCov G X k w) (coarseMean G X k w) (awakening i P D k.penalty F) q

include hd
lemma accepted (h : P.Branches k G) (u : f.val=c.val*P.L.val)
    (M : FreeResolvent.FaceRow) (hM : Whole M) (hm : ∀ i,(M.acts i).IsSymm)
    (U : Matrix (Body 1 f) (Body 1 c) ℝ) (hu : Inputs (linked P k c f u) U ((pink k.penalty w).acts f) (M.acts c))
    (he : Gets F) (hb : Halt F) (hF : Faithful (quad G (YM.RG08.hessian (pink k.penalty w))) F f) :
    let F' := veil P k X w i D (some c) F
    Decked F' ∧ (∀ i j,Tunable (F' i j)) ∧ Beacon c F' (quad G (YM.RG08.hessian M)) ∧ Faithful (quad G (YM.RG08.hessian M)) F' c := by
  intro F'
  let S:=linked P k c f u; let T:= X.forest S.ratio; let M':= pink k.penalty w
  have hE : Whole M':=(heart_saves k.penalty k.penalty_pos P.order_cut (id : Train P.J→_)).1.whole w
  have hZ (x) : (M'.acts x).IsSymm:= (origins_psd _ k.penalty_pos P.order_cut w x).1.eq
  let κ:S.Choices:= Classical.arbitrary _
  have hh:=(conditional_truth G X k w h).1
  have hC: Whole (coarseMean G X k w) := (hh.prod ((probe_recites G P k).1.flipped)).weight _
  obtain ⟨hv,hz⟩:=exhale_deck hh hC (Gets_awake P D k i he) (some c)
  let Q := quad G (YM.RG08.hessian M)
  have hP : Beacon c F' Q := by
    intro n v w' ha hy hp
    obtain ⟨V,hx⟩:=costumed hF n
    have hg := forest_precision G k w c f u h T
    have hW j:= (hx j).word
    have hj : Opinion S T κ V n v w' := by
      rcases hp with ⟨s,hs⟩| ⟨b,z,hb,hz⟩
      · exact signed_vote S T s h hW hs
      exact gaugeOpinion S T h hW b z hb hz
    obtain ⟨e,hY,ht,hC,hB⟩:=hj
    exact bless S G T U v w' κ n V F F' M' M i D hd h hx he hb hE hM hZ hm hu hg (fun v=> stationary_era G k i D P X w u M U hu h v F he (snow G T)) ha hy e hY ht hC hB
  refine ⟨hv,hz,hP,?_⟩
  have he' i j : Tunable (excise F' i j) := by unfold excise; split; apply Tunable.zero; exact hz i j
  have hh := opines_true (excise_beacons Q F' hP) (excise_below hv) (excise_heap _) he' (price_stanza G hM hm c).1
  intro e n; obtain ⟨f,hf,hQ⟩:= hh e n; refine ⟨_,hf,fun j hj=>?_⟩
  rw [hQ j hj]
  congr 1

end YM.RG08.Reflect
