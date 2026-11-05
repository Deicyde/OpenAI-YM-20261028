import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Heir.Border

/-! # Joint chart germs at a localized but possibly winding component

All numerical tests here are for the SAME marginal & mean as in the
inherited expectation. The E path needs joint smoothness with the Z
variables for our local differentiation-under-∫ proof, not only fixed-Z
budgets. Pose via separate already returned fine group log response in
each pane, then assemble entire argument fields (including those where E
happens to vanish) to use the actual E order without costly per-edge
sums. Non-E fields, e.g. state-dependent likelihoods or moving
localization tags, STILL have to be integrated by other works. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.JointLoad.Heir
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure Planned.AtomRegular.Foliage MultiNext.SignedSource WardBin.Lies
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {Pt : Teller G} {k : S.Choices} {V : Config G c} {F : Forest S.ratio}
    {P B : BudgetPoint} {i : Bond f} {g : Site c → G.El} {X : Support f} {Y : Support c} {Q C r x : ℝ} {I : Type}
    {A : Stores S} {n : ℕ} {q : Chi} {d u : ℝ} {f' : Config G f → ℝ}

abbrev outfit (G : Gauge) (f c : Side) := Bond f → Site c → G.El

structure Panes (S : StepData c f) (V : Config G c) (x : ℝ) (X : Support f) (P : BudgetPoint) (n : ℕ) (C : ℝ) (g : outfit G f c) : Prop where
  fits i : Mom.needed X i → Canvas P (S.ratio.parent i.1) (reach x) V (g i) n C

lemma framed (a : Museum F x A X Y I) (h : Healthy P.threshold Y V) (he : 100*(1+radiusB x)≤c.val) {Z : Collar G n} (hn : 1≤ n) (hz : Cube.Wire P (reach x) Z) :
    ∃ g : outfit G f c, Panes S V x X P n (Cube.fee Z) g := by
  choose! g hg using (fun i : Bond f => fun hi : Mom.needed X i => a.canvas _ (Finset.mem_union_left _ hi.1) h he Z hn hz); exact ⟨_,⟨hg⟩⟩

namespace Museum
variable [Fintype I] {w : Prices G I} (a : Museum F x A X Y I)
variable (T k V w u)
def pane (g : Site c → G.El) (i : Bond f) (z : Config G c) (w' : Prices G I) : Echo G c f := let b := crop (S.ratio.parent i.1) (reach x) g
    ((b z, a.extra g u w'),(b V, a.extra g u w))

def overt (g' : outfit G f c) (z : Config G c) (w' : Prices G I) : Directions G f := fun i => if Mom.needed X i then reply T F x k (g' i) i (a.pane V u w (g' i) i z w') else 0

lemma overt_home (g' : outfit G f c) : a.overt T k V u w g' V w=0 := by funext i; unfold overt; split; exact reply_self ..; rfl
variable {T k V w u}

variable {E : Type*} [TopologicalSpace E] {H : E → Config G c} {W : E → Prices G I} {p : E} {g' : outfit G f c}
  (hT : Act T F x k n r Q) (b : Folio.Bulletin x Pt T) (h : Panes S V x X P n C g') (U : Config G f)
  (hC : 1≤C) (ht : loom P (reach x) C < r) (hw : ∀ g : Site c→G.El, ‖a.extra g u w‖ ≤ loom P (reach x) C)
include hw hC ht h
lemma pane_inside (hi : Mom.needed X i) : ‖a.pane V u w (g' i) i V w‖ < r :=
    max_lt ((max_le ((h.fits i hi).paid hC) (hw _)).trans_lt ht) ((max_le ((h.fits i hi).paid hC) (hw _)).trans_lt ht)
include b hT
lemma overt_at (hH : Tendsto H (𝓝 p) (𝓝 V)) (hW : ∀ i, Mom.needed X i → Tendsto (fun z => a.pane V u w (g' i) i (H z) (W z)) (𝓝 p) (𝓝 (a.pane V u w (g' i) i V w))) :
    ∀ᶠ z in 𝓝 p, Agrees X (a.received k T q d u (H z) U (W z))
      (increment (a.received k T q d u V U w) (a.overt T k V u w g' (H z) (W z))) := by
  letI := Classical.decEq I
  apply eventually_all.mpr; intro i; by_cases hi : Mom.needed X i
  swap; exact Eventually.of_forall fun _ hx hy => False.elim (hi ⟨hx,hy⟩)
  have hv := h.fits i hi; have he := hW i hi
  filter_upwards [hH.eventually hv.seen, he.norm.eventually (gt_mem_nhds (pane_inside a h hC ht hw hi))] with z hz hZ
  intro _ _
  rw [increment,overt,if_pos hi]
  exact a.relative_read _ u b hT (Finset.mem_union_left _ hi.1) (Finset.mem_union_left _ hi.2) (a.asks_origin hi.1) (by rw [separation_self]; omega) _ _ U hz hv.seen.self_of_nhds hZ.le

lemma joint_overt : let h (p : Directions G c × Prices G I) := a.overt T k V u w g' (increment V p.1) p.2
    let H (p : Directions G c × Prices G I) := a.received k T q d u (increment V p.1) U p.2
    ContDiffAt ℝ n h (0,w) ∧ ∀ᶠ z in 𝓝 ((0,w): Directions G c × Prices G I), Agrees X (H z) (increment (a.received k T q d u V U w) (h z)) := by
  intro e H
  let Z i (p : Directions G c × Prices G I) := a.pane V u w (g' i) i (increment V p.1) p.2
  have ht' i (hi : Mom.needed X i) : ContDiffAt ℝ ω (Z i) (0,w) :=
    (((h.fits i hi).germ.comp (f:=Prod.fst (β:=Prices G I)) (0,w) contDiffAt_fst).prodMk ((a.extra _ u).contDiff.contDiffAt.comp _ contDiffAt_snd)).prodMk contDiffAt_const
  have he i : Z i (0,w)=a.pane V u w (g' i) i V w := by unfold Z; rw [Work.G07.at_zero_increment]
  refine ⟨contDiffAt_pi.mpr (fun i => ?_),a.overt_at hT b h U hC ht hw (H:=fun p : Directions G c × Prices G I => increment V p.1) (W:=fun p => p.2) ?_ (fun i hi => by rw [←he]; exact (ht' i hi).continuousAt.tendsto)⟩
  · dsimp only [e,overt]; split; swap; exact contDiffAt_const
    next hi => exact (G.adjoint _).toContinuousLinearMap.contDiff.contDiffAt.comp (g:=⇑(G.adjoint _).toContinuousLinearMap) _ (contDiffAt_pi.mp
        (((hT.calibrated.uniform _ ((he i).symm ▸ (pane_inside a h hC ht hw hi).le)).smooth).comp (f:=Z i) _ ((ht' i hi).of_le le_top)) i)
  have he := (show Continuous (fun p : Directions G c × Prices G I => increment V p.1) by unfold increment; fun_prop).tendsto (0,w)
  rwa [Work.G07.at_zero_increment] at he

lemma joint_receives (hB : B.Regular X f') (hn : n ≤ B.order) (hz : Healthy B.threshold X (a.received k T q d u V U w)) :
    ContDiffAt ℝ n (fun z : Directions G c × Prices G I => f' (a.received k T q d u (increment V z.1) U z.2)) (0,w) := by
  obtain ⟨hp,hh⟩ := a.joint_overt (d:=d) (q:=q) hT b h U hC ht hw
  let J (p : Directions G c × Prices G I) := a.overt T k V u w g' (increment V p.1) p.2
  have hJ : J (0,w) =0 := by unfold J; rw [Work.G07.at_zero_increment,a.overt_home]
  exact ((show ContDiffAt ℝ (↑n) (f' ∘ increment (a.received k T q d u V U w)) (J (0,w)) by rw [hJ]; exact (hB.smooth _ hz).of_le (Nat.cast_le.mpr hn)).comp (f:=J) _ hp).congr_of_eventuallyEq (hh.mono (fun _ hz => hB.sites _ _ hz))
end Museum
end YM.PhysicalNext.JointLoad.Heir
