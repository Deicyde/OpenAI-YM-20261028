import YM.RG08.Loom.Lease
/-!
# Literal cover-Ward, for any cutoff history with the right canonical quadratic
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Loom
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent Profiles
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge}{c f m : Side}{D n j h τ e r : ℕ}{R : ℝ} {S : Patch}
variable {U V : BoardU D R G} {F : Air G}{P : Patch}{K : KernelChoices}{W:Repeated P.L}{w : Train P.J}{i:G.ColorIndex}{σ : ChartRatio G}
local notation "X_[" p "," U "]" => filament P K w σ i W F p U τ h
lemma period_flights (he : P.Branches K G)(hp:1/2≤R)(ht : ∀ i j,Tidy (U i j))(hx:Fits τ U)(hF : Gets F) :
    let U' p:= filament P K w σ i W F p U τ h
    (∀ p,Fits τ (U' p) ∧ ∀ e r,Tidy (U' p e r)) ∧ ∀ m:ℕ→Side,Tendsto (fun i=>(m i).val) atTop atTop→
      ∀ e r, Hurled (fun i=> U' (some (m i)) e r) (U' none e r) := by
  intro U'
  have hK:= (conditional_truth G W K w he).1; have hm: Whole (coarseMean G W K w) := (hK.prod ((probe_recites G P K).1.flipped)).weight _
  have hA:= Gets_awake P σ K i hF; have ⟨_,hC⟩:= creamy h P.L hx (fun i j=>(ht i j).pens) hp P.odd_side
  exact ⟨fun p=> filops_charge hx (fun i j=>(ht i j).pens) hp P.odd_side hK hm hA.1 (fun i j=> hA.2 i j|>.1), fun m he e r=> (WashHurled (U:=fun i=> cream h U P.L) m (fun i j=> Hurled.fixed (hC i j|>.pens)) hA (veiled_whole hK) he).spring (scan_whole hm)⟩

def framesOK (K M : FreeResolvent.FaceRow)(P : Patch)(k : KernelChoices) := Whole M ∧ (∀ i,(M.acts i).IsSymm) ∧ ∀ c f (h:f.val=c.val*P.L.val),∃ x : Matrix (Body 1 f) (Body 1 c) ℝ, Inputs (linked P k c f h) x (K.acts f) (M.acts c)

private def height (m : ℕ) : Side := ⟨m+1,Nat.succ_pos _⟩
private lemma ratchet (m : Side) : Tendsto (fun i=> (height i * m).val) atTop atTop := by
  refine tendsto_atTop_mono ?_ (tendsto_add_atTop_nat 1); intro i; change i+1≤ (i+1)*m.val; exact Nat.le_mul_of_pos_right _ m.property

theorem slotted (hc : LocalRatio σ)(he : P.Branches K G)(hp:1/2≤R)(ht : ∀ i j,Tidy (U i j))(hx:Fits τ U)
    (B : FreeResolvent.FaceRow)(hB : framesOK (pink K.penalty w) B P K)(hF : Gets F)(hO : Halt F)(hv : ∀ n,Faithful (quad G (YM.RG08.hessian (pink K.penalty w))) F n)(hU : ∀ f,Parade f τ U) (c m : Side) : Parade m τ (filament P K w σ i W F none U τ h) := by
  let s i:= height i * m; let g (i:ℕ) : Ratio (height i) (s i):=⟨m,rfl⟩
  let X i' := X_[some (s i'),U]; have ⟨u,v⟩:= period_flights (W:=W) (w:=w) (h:=h) (σ:=σ) (i:=i) he hp ht hx hF
  apply Parade.moving (v s (ratchet m)); intro a φ o
  let E:=g a; let z:= E.assemble (0,o)
  obtain ⟨Y,hY⟩:= hB.2.2 (s a) (s a * P.L) rfl
  have hs:= wove (X:=W) (i:=i) (c:=s a) (f:=s a * P.L) rfl hc he hB.1 hB.2.1 hY (hv _) hF hO ht hx hp h (hU _) φ z
  have hy := shore_travel (fun j k=> plug φ R∘X a j k) E z (fun j k=> ((u (some (s a))).2 j k|>.pens|>.shaped _)) hs
  rw [show E.residue z=o from E.assemble_res ..] at hy; exact hy

theorem standing (hc : LocalRatio σ)(he : P.Branches K G)(hp:1/2≤R)(ht : ∀ i j,Tidy (U i j))(hx:Fits τ U)
    (hV : Fits τ V) (hg : ∀ i j,Tidy (V i j)) (B : FreeResolvent.FaceRow)(hB : framesOK (pink K.penalty w) B P K)(hF : Gets F)(hO : Halt F)(hv : ∀ n,Faithful (quad G (YM.RG08.hessian (pink K.penalty w))) F n)(hU : ∀ f,Parade f τ U) (s : Signed)(hS : ∀ m,Honor s U V m)(m : Side) : Honor s X_[none,U] X_[none,V] m := by
  let v i:= height i*m; let g (i:ℕ): Ratio (height i) (v i):=⟨m,rfl⟩
  have h₀ :=period_flights (W:=W) (w:=w) (h:=h) (σ:=σ) (i:=i) he hp ht hx hF
  have h₁ := period_flights (W:=W) (w:=w) (h:=h) (σ:=σ) (i:=i) he hp hg hV hF
  apply Honor.moving (h₀.2 v (ratchet m)) (h₁.2 v (ratchet m)); intro a
  obtain ⟨Y,hY⟩ := hB.2.2 (v a) (v a * P.L) rfl
  refine slant_travel (g a) (attend (f:=v a*P.L) rfl hc he hB.1 hB.2.1 hY (hv _) hF hO ht hg hx hV hp h (hU _) s (hS _)) (fun j k=> ?_) (fun j k=> ?_)
  exacts [(h₀.1 (some (v a))).2 j k|>.pens,(h₁.1 (some (v a))).2 j k|>.pens]
end YM.RG08.Loom
