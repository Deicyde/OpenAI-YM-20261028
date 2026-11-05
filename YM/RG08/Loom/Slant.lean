import YM.RG08.Loom.Bell
/-!
# Covariance of single-label packet on the same finite period exact
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
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent Profiles PertExtension.Chart
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {p c f : Side} {G : Gauge}
variable {M : Matrix (Body 1 f) (Body 1 c) ℝ} {v w : ℝ→Link G c} {n h j τ e : ℕ} {k : KernelChoices} {D : ℕ}{R : ℝ} {φ φ' : Exam D}
variable {U U' : BoardU D R G} {V : ℕ→ Config G f→ℝ}{F F' : Air G} {B K : FreeResolvent.FaceRow} {σ : ChartRatio G} {o o' : Site c} {i : G.ColorIndex}

variable {P : Patch} {X : Repeated P.L} {w' : Train P.J}

def filament (A : Patch)(k : KernelChoices)(w' : Train A.J)(σ : ChartRatio G)(i : G.ColorIndex) (B' : Repeated A.L) (F : Air G) (p : Option Side) (U : BoardU D R G) (τ h : ℕ) :=
    filop (conditionalCov G B' k w') (coarseMean G B' k w') (awakening i A σ k.penalty F) p τ h U
local notation "X_" U => filament P k w' σ i X F (some c) U τ h
private lemma size_chart {g : ℝ→ Link G c} (V : Reel (Psalm (Lines G c 1)))(h : ∀ i,Grass (V i))(hp : AnalyticAt ℝ g 0) : ∀ j,Bill 0 (fun t=> V j (g t)) := fun i=> life_price (((h i).smooth.continuous.continuousAt.comp hp.continuousAt).mono_left nhdsWithin_le_nhds)
lemma lank (he : f.val=c.val*P.L.val) (hp : LocalRatio σ) (hk : P.Branches k G)
    (hB : Whole B) (hM : ∀ m,(B.acts m).IsSymm)
    (hX : Inputs (linked P k c f he) M ((pink k.penalty w').acts f) (B.acts c))
    (hV : ∀ i,Caper (quad G (YM.RG08.hessian (pink k.penalty w'))) F (τ+n) i (V i)) (hF : Gets F)(ht:Halt F)
    (hU : ∀ i j, Tidy (U i j))(hU' :∀ i j,Tidy (U' i j)) (hP:Fits τ U)(hQ : Fits τ U')
    (hO:1/2 ≤ R)
    (hv : AnalyticAt ℝ v 0) (hw : AnalyticAt ℝ w 0) :
    let S:=linked P k c f he
    let T:=X.forest S.ratio
    ∀ (W W' : Site S.ratio.count→ℕ→ Config G f→ℝ), (∀ p j,Cargo (S.ratio.assemble (o,p)) τ j (τ+n+τ) (fun i l=> plug (Pages.roll (spinner p) (P.L.val:ℝ)⁻¹ φ) R ∘ U i l) (W p j))→(∀ p j,Cargo (S.ratio.assemble (o',p)) τ j (τ+n+τ) (fun i l=> plug (Pages.roll (spinner p) (P.L.val:ℝ)⁻¹ φ') R ∘ U' i l) (W' p j))→
      ∀ (g : ℝ →(T.Slice G≃ₜT.Slice G)) (κ : S.Choices), WalkPays S G T g κ (τ+n) h τ v w V W W' →
    Fit (n+1) (arco c (fun j=> large o (τ+j) (fun r=> plug φ R ∘ (X_ U) j r)) v n)
        (arco c (fun j=> large o' (τ+j) (fun r=> plug φ' R ∘ (X_ U') j r)) w n) := by
  intro S T W W' hW hW' g κ ht'
  let K:=pink k.penalty w'; have hδ:= forest_precision G k w' c f he hk T
  have hL := carrying S G T (M:=M) (K:=K) hp hk hX ((heart_saves k.penalty k.penalty_pos P.order_cut (id : Train P.J→_)).1.whole w') hB (fun x=> (origins_psd _ k.penalty_pos P.order_cut w' x).1.eq) hM hδ hV hF ht
    (U':=filament P k w' σ i X F (some c) U τ h) (H':=filament P k w' σ i X F (some c) U' τ h) (F':=Reflect.veil P k X w' i σ (some c) F) (fun x=>stationary_era G k i σ P X w' he B M hX hk x F hF (snow G T)) hW hW' (fun i j=>(hU i j).pens) (fun i j=>(hU' i j).pens) hO
    (fun t=> onValve G P k w' he M o B hX i σ X F hF hk φ hO hP (fun i j=>(hU i j).pens) h t) (fun t=> onValve G P k w' he M o' B hX i σ X F hF hk φ' hO hQ (fun i j=>(hU' i j).pens) h t) g hv hw ht' -- g explic
  exact licensed (size_chart _ (fun i=>dryL ..) hv) (size_chart _ (fun i=>dryL ..) hw) (Eq.refl (τ+n)) hL

lemma wove (he : f.val=c.val*P.L.val) (hp : LocalRatio σ) (hk : P.Branches k G)
    (hB : Whole B) (hM : ∀ m,(B.acts m).IsSymm)
    (hX : Inputs (linked P k c f he) M ((pink k.penalty w').acts f) (B.acts c))
    (hV : Faithful (quad G (YM.RG08.hessian (pink k.penalty w'))) F f)(hF : Gets F)(ht:Halt F)(hU : ∀ i j, Tidy (U i j))(hP:Fits τ U)(hO:1/2 ≤ R)(h : ℕ)
    (hz : Parade f τ U) : Parade c τ (filament P k w' σ i X F (some c) U τ h) := by
  let S:= linked P k c f he; let T := X.forest S.ratio
  intro φ o v w hv hw hy n; dsimp only
  obtain ⟨V,hV⟩:= costumed hV (τ+n)
  let Wt (p:Site S.ratio.count):= (fun i l=> plug (Pages.roll (spinner p) (P.L.val:ℝ)⁻¹ φ) R ∘ U i l)
  choose W hW using fun (p:Site S.ratio.count)(j:ℕ)=> shelved (p:=j) (hz _ (S.ratio.assemble (o,p)) : Shore (S.ratio.assemble (o,p)) τ (Wt p)) (by omega : τ ≤ τ+n+τ+j) (fun i j=> Tidy.map _ (hU i j))
  let κ : S.Choices := Classical.arbitrary _
  obtain ⟨u,hu⟩:= sails_gauge S G T (κ:=κ) (fun i=> (hV i).word) hk (fun a b=>(hW a b).toShell) hy h (τ+n) τ
  exact lank he hp hk hB hM hX hV hF ht hU hU hP hP hO hv hw W W (hW) hW u κ hu

section spin
variable {U V : Screed ℝ (Loc G 1)}
lemma spin_shell (s : Signed) {W:Config G f→ℝ}(h : Shell G f W) : Shell G f (W ∘ pull s 0) := by
  let T:= orderTurn (G:=G) (m:=f) s
  let X := fun x : Link G f=> W (pull s 0 (input G f x)); have he : X=(W∘input G f)∘T := funext fun x=>congr_arg W (flip_links ..)
  constructor
  · exact h.measure.comp (continuous_pull s (0:Site f)).measurable
  · change ContDiffAt ℝ ω X 0; rw [he]; exact ((map_zero T).symm ▸ h.hol).comp _ T.contDiff.contDiffAt
  intro A x y k l hx hy hh
  have hK := pullers_one (f:=f) G s
  apply h.coast (l:=l) (v:=pull s 0∘ x) (w:=pull s 0 ∘ y) (g:=fun a=> (k a ∘ Lattice.affine s 0)) _ _ _
  · exact hK.comp hx
  · exact hK.comp hy
  filter_upwards [hh] with a ha; simp only [Function.comp_apply,ha,Work.F05.pull_gauge_zero]; rfl
-- build rotated witness for V given U after spin orientation
lemma rotates_shell {W:Config G c→ℝ}(s : Signed) (hs:Cargo o τ j n U W) (hv : DiscSpin s o o' U V)
    (hV : ∀ i k,Tidy (V i k)) : Cargo o' τ j n V (W ∘ pull s⁻¹ 0) := by
  let T:= orderTurn (G:=G) (m:=c) s; let K:= orderTurn (G:=G) (m:=c) s⁻¹; let f:=W∘pull s⁻¹ 0; have hf := spin_shell s⁻¹ hs.toShell
  refine ⟨hf,fun p hh=> ?_⟩
  have H:=hf.hol
  apply Tensor.ext_diag _ _ (Tensor.coeff_symm (H.of_le le_top)) ((strand_tid hV).sym _) -- fix `le_top`
  funext x
  have he: f∘input G c=(W ∘input G c)∘K:= funext fun x=>congr_arg W (flip_links ..)
  change Tensor.diagonal (Tensor.coeff (f ∘ input G c) _ _) x=_
  rw [he]; unfold Tensor.coeff Tensor.diagonal; rw [Next.Foundations.jets_linear K (hs.hol.of_le le_top)]
  change Tensor.diagonal (Tensor.coeff (W∘input G c) p 0) (K x)=rootSong (strand τ j V p) c o' x
  rw [hs.scores_at p hh]; unfold strand; split
  next h=>
    refine Eq.trans (hv _ _ (K x)) (congr_arg (fun x => rootSong (V _ p) c o' x) ?_)
    change T (K x)=x
    have hh y : input G c (T (K y))=input G c y := Eq.trans (Eq.symm (flip_links ..)) ((congr_arg (pull s (0:Site c)) (Eq.symm (flip_links ..))).trans ((signedWalk G c s).apply_symm_apply _))
    have hn: Tendsto (fun t:ℝ=> t•x) (𝓝[>]0) (𝓝 0) := by simpa using! ((continuous_id.smul (continuous_const (y:=x))).tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
    have hI : Tendsto (fun t:ℝ=> T (K (t•x))) (𝓝[>]0) (𝓝 0) := (T.continuous.tendsto' 0 0 (map_zero _)).comp ((K.continuous.tendsto' 0 0 (map_zero _)).comp hn)
    obtain ⟨t,hp,h,q⟩:= (eventually_pos.and ((hI.eventually input_encodes).and (hn.eventually input_encodes))).exists
    apply smul_right_injective (Link G c) hp.ne'
    dsimp only; rw [← map_smul T,← map_smul K] -- wrong
    exact h.symm.trans ((congr_arg content (hh (t•x))).trans q)
  next h=> simp [Tensor.diagonal]
end spin
end YM.RG08.Loom
