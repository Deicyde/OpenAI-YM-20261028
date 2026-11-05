import YM.Extra.ITERATION_NO_LOSS.Transport

/-!
# Remaining jets for a calibration step

These statements *do not provide* the fresh classical tensors or the
one-loop determinant calculation. They check the jet/readout separation and
sufficiency of doing the remaining computation on one forest and one tag per
period. Use F03--5; never assume the gap, alpha, or tree data of two histories
can be mixed after a match. All actions in these tests are functions on their
actual configurations, counting convention as in Precision.Loop.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.Iteration.Calibration
open Filter Function Lattice Wilson RG Exterior Precision Tree Bloch Bid Matrix Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius InnerProductSpace

variable {G : Gauge} {n c f : Side} {S : StepData c f}

abbrev jet {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (j : ℕ) (f : X → ℝ) := iteratedFDeriv ℝ j f 0
lemma jet_add {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (j : ℕ) {f g : X → ℝ}
    (hf : ContDiffAt ℝ ω f 0) (hg : ContDiffAt ℝ ω g 0) : jet j (f+g) = jet j f + jet j g :=
  iteratedFDeriv_add_apply (hf.of_le le_top) (hg.of_le le_top)

abbrev acted {k : ℕ} (M : ℕ → Atom G k) (x : Dir G n) := action M (represent x)
abbrev core (W : PathData G) (p : Clip) (x : Dir G n) := secondTerm p W (represent x)
abbrev main (W : PathData G) (p : Clip) (x : Dir G n) := mainTerm p W (represent x)

lemma splits (W : PathData G) (p : Clip) : main (n:=n) W p = core W p + acted W.cubic + acted W.quartic := by
  funext x; simp only [Pi.add_apply,main,core,acted,mainTerm,secondTerm,Patch.average,action, Finset.sum_add_distrib,mul_add]

lemma acted_jet {k : ℕ} {η C : ℝ} (M : ℕ → Atom G k) (he : 0 < η) (h : Charged M η C) : ContDiffAt ℝ ω (acted (n:=n) M) 0 :=
  action_smooth he h fun i => (Work.F03.represent_smooth i).contDiffAt
lemma main_jet {W : PathData G} {σ C Λ : ℝ} {p : Clip} (h : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (main (n:=n) W p) 0 :=
  Work.F02.mainTerm_contDiffAt h fun i => (Work.F03.represent_smooth i).contDiffAt
lemma core_jet {W : PathData G} {σ C Λ : ℝ} {p : Clip} (h : W.Bounds p σ C Λ) : ContDiffAt ℝ ω (core (n:=n) W p) 0 := by
  rw [show core (n:=n) W p = main W p - acted W.quartic - acted W.cubic by rw [splits]; abel]
  exact ((main_jet h).sub (acted_jet _ h.width h.four)).sub (acted_jet _ h.width h.three)

abbrev actual (H : Forest S.ratio) (t : S.Choices) (p : Clip) (W : PathData G) (ρ : Dir G c → AxisChart G H)
    (x : Dir G c) := tested H t p W x (ρ x)
abbrev aged {k : ℕ} (M : ℕ → Atom G k) (H : Forest S.ratio) (ρ : Dir G c → AxisChart G H)
    (x : Dir G c) := action M (liftedTo H ρ x)

lemma actual_jet {H : Forest S.ratio} {p : Clip} {W : PathData G} {ρ} (h : Critical H p W ρ) (t : S.Choices) :
    ContDiffAt ℝ ω (actual H t p W ρ) 0 := by
  have he := (h.2.2 t).1; rw [show (0 : Dir G c × AxisChart G H)=((0:Dir G c),ρ 0) by rw [h.1]; rfl] at he
  exact he.comp (f:=fun x => (x,ρ x)) _ (graph_jet _ h.2.1)

lemma top_lower (P : Bed) (u v : ℝ) {W : PathData G} {p σ C Λ} (h : W.Bounds p σ C Λ) (hf : Floor P p n u v) (ht : Attached P W)
    (hs : Sworn P n G) (hP : P.diagonal.acts n=1) : ∀ j ≤ 2, SameJet j (main (n:=n) W p) (energy ∘ represent) := by
  have he (x : Dir G n) : gaugeFiscal P x x = ∑ b : Face (Per n), ‖Work.F03.faceCurl b x‖^2 := by
    rw [Channel.fiscal_flux]
    simp_rw [mulVec_mulVec, hf.same,hP, Matrix.one_mul, dotProduct]; rw [Finset.sum_comm, ← Equiv.sum_comp (Equiv.prodCongr (Equiv.refl (Site n)) plaqEquiv)]
    apply Finset.sum_congr rfl; intro b _
    rw [← real_inner_self_eq_norm_sq, Work.F03.inner_color]; rfl
  refine Jets.leading (main_jet h) ?_ (fun x => Work.F03.main_limit h ht hf hs x) (fun x => ?_)
  · refine ContDiffAt.sum fun b _ => Work.F03.price_smooth (A:=fun (x : Dir G n) => faceValue (represent x) b) ?_
    simp_rw [faceValue,← Work.F02.stringMat_physical]; exact ((Work.F02.stringMat_contDiff (G:=G) _ _).restrict_scalars ℝ).contDiffAt.comp
      (f:=fun x : Dir G n => Work.F02.physical (represent x)) 0 (Work.F02.physical_contDiffAt fun i => (Work.F03.represent_smooth i).contDiffAt)
  unfold Function.comp Wilson.energy
  simp_rw [he,Finset.sum_div]; exact tendsto_finsetSum _ (fun b _ => Work.F03.price_limit (G:=G) (V:=fun t : ℝ => faceValue (represent (t • x)) b)
    (by rw [zero_smul]; exact Push.stroll_zero ..) (Work.F03.face_deriv b x))

lemma lower (P Q : Bed) {R T : PathData G} {p q σ σ' C C' Λ Λ' u v w z} {H : Forest S.ratio} (hl : Larger (G:=G) S)
    (h : R.Bounds p σ C Λ) (h' : T.Bounds q σ' C' Λ') (hf : Floor P p f u v) (hc : Floor Q q c w z) (ht : Attached P R) (ht' : Attached Q T)
    (hs : Sworn P f G) (hs' : Sworn Q c G) {ρ} (hr : Critical H p R ρ) (hQ : HeatG H p R ρ Q) (a : S.Choices) :
    ∀ j ≤ 2, SameJet j (actual H a p R ρ) (main T q) := by
  have hF := ((YM.Work.F03.answer G _ _ S hl H P p R _ _ _ _ _ hf h ht hs (YM.Work.F02.answer G p R σ C Λ h)).2 a)
  let F := Function.uncurry (tested H a p R); let r (x : Dir G c) := (x,ρ x)
  have hr0 : r 0 = 0 := Prod.ext rfl hr.1
  have h0 : actual H a p R ρ 0 = 0 := by change F (r 0)=0; rw [hr0]; exact hF.1
  have hg : fderiv ℝ (actual H a p R ρ) 0 = 0 := by
    change fderiv ℝ (F ∘ r) 0=0
    rw [fderiv_comp _ (show DifferentiableAt ℝ F (r 0) from hr0.symm ▸ (hr.2.2 a).1.differentiableAt (by simp))
      ((graph_jet _ hr.2.1).differentiableAt (by simp)),hr0,show fderiv ℝ F 0=0 from hF.2.1, ContinuousLinearMap.zero_comp]
  let g (x : Dir G c) := (1/2:ℝ)*gaugeFiscal Q x x
  have hga : ContDiffAt ℝ ω g 0 := (hQ a).2.1
  have hscale (t : ℝ) (x : Dir G c) : g (t • x) = g x * t^2 := by
    unfold g gaugeFiscal; rw [mul_assoc, Finset.sum_mul]; congr 1; apply Finset.sum_congr rfl; intro i _
    rw [show parts G 1 (t • x) i=t • parts G 1 x i from rfl, Matrix.mulVec_smul,dotProduct_smul, smul_dotProduct,smul_eq_mul,smul_eq_mul]; ring
  have hQx : ∀ i ≤ 2, SameJet i (main (n:=c) T q) g := Jets.leading (main_jet h') hga (fun x => Work.F03.main_limit h' ht' hc hs' x) fun x => by
    apply tendsto_const_nhds.congr'
    filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 from self_mem_nhdsWithin] with t ht
    rw [hscale]; unfold g; field_simp
  have hv := Jets.negligible (d:=1) (hga.of_le le_top) (fun x => Jets.drop one_lt_two (a:=g x) (by
    apply tendsto_const_nhds.congr'; filter_upwards [show ∀ᶠ t : ℝ in 𝓝[≠] 0, t ≠ 0 from self_mem_nhdsWithin] with t ht; rw [hscale]; field_simp))
  intro j hj; refine ⟨actual_jet hr _,main_jet h',?_⟩
  change jet j _ = _; rw [(hQx j hj).2.2]
  interval_cases j
  · rw [hv 0 (by decide)]; ext1 m; rw [iteratedFDeriv_zero_apply,h0]; rfl
  · rw [hv 1 le_rfl]; ext1 m; rw [iteratedFDeriv_one_apply,hg]; rfl
  · exact (hQ a).2.2

/-- Fresh pieces after taking out the calculated leading substitutions; in the
fourth equation the *whole actual emitted cubic* (including its paths) is used. -/
structure Fresh (H : Forest S.ratio) (a : S.Choices) (R T : PathData G) (p q : Clip) (ρ : Dir G c → AxisChart G H)
    (E : ℕ → Atom G 3) (V : ℕ → Atom G 4) : Prop where
  three : jet 3 (actual H a p R ρ) = jet 3 (core (n:=c) T q) + jet 3 (acted E) + jet 3 (aged R.cubic H ρ)
  four : jet 4 (actual H a p R ρ) = jet 4 (core (n:=c) T q) + jet 4 (acted T.cubic) + jet 4 (acted V) + jet 4 (aged R.quartic H ρ)

lemma higher (R T : PathData G) {p q σ C Λ} {H : Forest S.ratio} (h : T.Bounds q σ C Λ)
    {E F : ℕ → Atom G 3} {V W : ℕ → Atom G 4} {B D B' D' : ℝ} (he : T.cubic=join E F) (hf : T.quartic=join V W)
    (hE : Charged E σ B) (hF : Charged F σ D) (hV : Charged V σ B') (hW : Charged W σ D')
    {ρ} (hr : Critical H p R ρ) {a} (ht : Fresh H a R T p q ρ E V)
    (h3 : SameJet 3 (aged R.cubic H ρ) (acted F)) (h4 : SameJet 4 (aged R.quartic H ρ) (acted W)) :
    ∀ j, 3 ≤ j → j ≤ 4 → SameJet j (actual H a p R ρ) (main T q) := by
  have hz (j : ℕ) : jet j (main (n:=c) T q) = jet j (core T q) + jet j (acted T.cubic) + jet j (acted T.quartic) := by
    rw [splits, jet_add j (f:=core T q + acted T.cubic) ((core_jet h).add (acted_jet _ h.width h.three)) (acted_jet _ h.width h.four),jet_add j (core_jet h) (acted_jet _ h.width h.three)]
  have hx {k : ℕ} (A B : ℕ → Atom G k) {u v} (hA : Charged A σ u) (hB : Charged B σ v) :
      acted (n:=c) (join A B) = acted A + acted B := funext fun i => action_join h.width hA hB _
  intro j lo hi; refine ⟨actual_jet hr _,main_jet h,?_⟩; change jet j _ = jet j _
  interval_cases j
  · rw [ht.three, show jet 3 (aged R.cubic H ρ)=_ from h3.2.2, hz 3, show jet 3 (acted (n:=c) T.quartic) = 0 from lower_jet (M:=T.quartic) h.width h.four 3 (by omega), add_zero, he,hx _ _ hE hF,
      jet_add 3 (acted_jet _ h.width hE) (acted_jet _ h.width hF), add_assoc]
  · rw [ht.four, show jet 4 (aged R.quartic H ρ)=_ from h4.2.2, hz 4, hf, hx _ _ hV hW, jet_add 4 (acted_jet _ h.width hV) (acted_jet _ h.width hW),add_assoc (_+_)]

end YM.Extra.Iteration.Calibration
