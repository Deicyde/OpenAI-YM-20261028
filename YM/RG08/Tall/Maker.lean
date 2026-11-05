import YM.RG08.Loom.Spool
/-!
# Enrollment of the invariant mark jet stencils. Projection should preserve
strands, not preserve invariance by each leg alone.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
noncomputable section
namespace YM.RG08.Tall
open Function Filter Lattice Wilson Exterior Bloch Next.Free Work.F08 RG Laurent Precision Finset
open Quire Stationary Scores Scores.Pages Matrix Push.AbsoluteSums PertExtension.Chart PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis Loom MeasureTheory
open scoped Topology ContDiff Classical BigOperators
variable {I α E : Type} {G : Gauge} {D p n r k τ ε j h Λ : ℕ} {m c f L : Side} {R : ℝ} {i : Site m}

lemma Shell.plus {W W': Config G m→ℝ}(h : Shell G m W) (hp : Shell G m W') : Shell G m (W+W') := ⟨h.measure.add hp.measure,h.hol.add hp.hol,fun v w k l hv hw hh=> ((h.coast _ _ _ _ hv hw hh).add (hp.coast _ _ _ _ hv hw hh))⟩ -- implicit
lemma Shell.scale {W: Config G m→ℝ}(h : Shell G m W)(a : ℝ) : Shell G m (a • W) := ⟨h.measure.const_smul a,h.hol.const_smul a,fun v w k l hv hw hh=> (Filter.EventuallyEq.refl _ (fun _=>a)).mul (h.coast _ _ _ _ hv hw hh)⟩
lemma shell_zero : Shell G m 0 := ⟨measurable_const,contDiffAt_const,fun _ _ _ _ _ _ _ => EventuallyEq.rfl⟩

variable {U V:Screed ℝ (Loc G 1)}{W W':Config G m→ℝ}
lemma unmask (x : Link G m) (u : ℕ) {g : ℝ→Link G m}(hp : AnalyticAt ℝ g 0) : Tendsto (fun t:ℝ=> input G m (t•g t)) (𝓝 0) (𝓝 1) := by simpa using! (input_cont.continuousAt.comp (g:=input G m) (continuousAt_id.smul hp.continuousAt)).tendsto
lemma vocalized (h : ∀ k,∃ W:ℕ→Config G m→ℝ,∀ j,Cargo i τ j (k+τ) U (W j)) : Shore i τ U := by
  intro v w hv hw hh k; obtain ⟨W,hW⟩:= h k; dsimp only
  obtain ⟨z,c,hz,H⟩:=hh; let p (x:ℝ→Link G m)(t:ℝ):= ∑ i∈range (k+τ+1),t^i* W i (input G m (t•x t)); let L e:=large i (τ+e) (U e)
  have he : Fit (τ+(k+1)) (p v) (p w) := by
    refine Fit.supply ?_ _; apply EventuallyEq.filter_mono ?_ nhdsWithin_le_nhds
    filter_upwards [(eventually_all_finset (range (k+τ+1))).mpr (fun j _=> (hW j).coast (fun t:ℝ=> input G m (t • v t)) (fun t:ℝ=>input G m (t • w t)) z _ (unmask 0 0 hv) (unmask 0 0 hw) H)] with x hx; unfold p; exact sum_congr rfl fun j hj=> congr_arg (x^j * ·) (hx j hj).symm
  have hP : Fit ((k+1)+τ) (fun t=>t^τ*arco m L v k t) (fun t=>t^τ *arco m L w k t) := by rw [add_comm]; exact (fileFit hv.continuousAt hW).turn.join (he.join (fileFit hw.continuousAt hW))
  refine Fit.join (Fit.supply ?_ _) (Fit.join (hP.shorten (k:=τ)) (Fit.supply ?_ _))
  · exact eventually_pos.mono (fun i hi=> Eq.symm (mul_div_cancel_left₀ _ (pow_pos hi _|>.ne')))
  exact eventually_pos.mono fun i hi=>mul_div_cancel_left₀ _ (pow_pos hi _|>.ne')

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

-- periods invariant ALL; not necessarily finite Ward gap
structure Marvel (τ : ℕ) (U : BoardU D R G) : Prop where
  cap : Fits τ U
  hem : ∀ i j,Tidy (U i j)
  wardrobe : ∀ m, Parade m τ U
lemma marvelled {U:BoardU D R G} {P : Patch} {K : KernelChoices} {T : Air G} {w : Train P.J}
    {B : FreeResolvent.FaceRow}{σ:ChartRatio G} (h : Marvel τ U) (hp: P.Branches K G)(ht:Gets T) (hz:1/2≤R)
    (hb : framesOK (pink K.penalty w) B P K)(hT : Halt T)(hm : ∀ f, Faithful (quad G (YM.RG08.hessian (pink K.penalty w))) T f)(ha:LocalRatio σ)(i:G.ColorIndex)(x:Repeated P.L)(k:ℕ) :
    Marvel τ (filament P K w σ i x T none U τ k) := by
  have ⟨hs,hE⟩:= (period_flights (W:=x) (w:=w) (h:=k) (i:=i) (σ:=σ) hp hz h.hem h.cap ht).1 none -- fix
  exact ⟨hs,hE,fun m=> slotted ha hp hz h.hem h.cap B hb ht hT hm h.wardrobe m m⟩

lemma Cargo.blank (i : Site m) (n k p : ℕ) : Cargo (G:=G) i k p n 0 0 := ⟨shell_zero,fun j hj=>by
    simp only [Tensor.coeff,show (0:Config G m →ℝ)∘input G m=0 from rfl,iteratedFDeriv_zero,Pi.zero_apply,smul_zero,Loom.strand]; split <;> simp⟩
lemma Cargo.added (A : Cargo i τ j n U W)(B : Cargo i τ j n V W') (h:∀ i r,Tidy (U i r))(p : ∀ i r,Tidy (V i r)) : Cargo i τ j n (U+V) (W+W') := by
  refine ⟨Shell.plus A.toShell B.toShell,fun x hx=>?_⟩
  rw [show (W+W')∘ input G m = (W∘input G m)+(W'∘input G m) from rfl,Tensor.coeff_add (A.hol.of_le le_top) (B.hol.of_le le_top),A.scores_at x hx,B.scores_at x hx]; unfold Loom.strand; split
  next he=> exact (st_plus (h _ x|>.pens.of_norm) (p _ x|>.pens.of_norm) _).symm
  next h=> simp
lemma Cargo.weight (A : Cargo i τ j n U W)(h:∀ i r,Tidy (U i r)) (b : ℝ) : Cargo i τ j n (b•U) (b • W) := by
  refine ⟨Shell.scale A.toShell b,fun x hx=>?_⟩
  rw [show (b • W)∘ input G m = b • (W∘input G m) from rfl,Tensor.coeff_smul _ (A.hol.of_le le_top),A.scores_at x hx]; unfold Loom.strand; split
  next he=> exact (st_scale b (h _ x|>.pens.of_norm) _).symm
  next h=> simp
lemma Shore.vessel (h : Shore i τ U)(hp:∀ i j,Tidy (U i j))(k) : ∃ W:ℕ→Config G m→ℝ,∀ j,Cargo i τ j (k+τ) U (W j) := by
  choose W hW using fun j:ℕ=> shelved (p:=j) h (show τ ≤ k+τ+j by omega) hp; exact ⟨W,hW⟩

-- explicit source algebra (trunc higher order separate)
end YM.RG08.Tall
