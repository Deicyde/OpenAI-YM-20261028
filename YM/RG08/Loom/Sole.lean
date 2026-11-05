import YM.RG08.Loom.Cargo
/-!
# Folding/passive laws into analytical consumers
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
open Quire Stationary Scores Matrix PertExtension.Series PertExtension.Series.Radial PertExtension.Series.Tested Shade Reflect Analysis MeasureTheory PertExtension.GaussianScore Tree FreeResolvent
open scoped Topology ContDiff Classical BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} {D j k τ h : ℕ} {m c f : Side} {R : ℝ}
variable {X β : Type} [Fintype X] [DecidableEq X] [Fintype β] [DecidableEq β]
variable {S' : Canticle β} {K' : Row β β}{V : Screed ℝ β}
section weights
lemma dryL (i : Site m)(P : Spine ℝ β) (n : ℕ) : Grass (large i n P) := Grass.list fun j _=> Grass.base (Hemi.pos (stitch _ _ _))
lemma wheat (P U : Reel (Psalm X)) (h : ∀ i,Grass (P i)) (hp : ∀ i,Grass (U i)) (j): Grass (billow P U j) := Grass.list fun i _=> (h _).times (hp _)
lemma consumes {M : Matrix X X ℝ} (hM : PosDef M)
    (μ:Measure (X →ℝ)) [μ.HasTemperateGrowth] [μ.IsAddRightInvariant] [NeZero μ]
    (hp : Whole K') (A : Matrix (Co c β) X ℝ) (hX : K'.acts c = A*M⁻¹*Aᵀ)
    (hS : Gets S')(hT : ∀ i r,Tidy (V i r))(hV:Fits τ V) (i : Site c) (x : PAC β c) :
    let U':= fun j=> large i (τ+j) (V j)
    let P := expEra (fun j=>grand (j+2) (S' j) c)
    let Q:= fun j=> large i (τ+j) (washed τ (some c) K' S' V j)
    ∀ j,leaned hM μ A x (billow U' P j)=∑ b∈wheel j,Q b.1 x*leaned hM μ A x (P b.2) := by
  intro U' P Q j; let H:=fun j=>grand (j+2) (S' j) c
  have hD : (K'.acts c)ᵀ=K'.acts c:= by
    rw [hX,Matrix.transpose_mul,Matrix.transpose_mul, transpose_transpose, show (M⁻¹)ᵀ=M⁻¹ by simpa using hM.inv.isHermitian.eq, Matrix.mul_assoc]
  obtain ⟨h₁,h₂,h₃⟩:= Quire.denominator i hp hD (fun i j=> hS.2 i j|>.1) hS.1 hT hV
  have hz:= (vertex_slope hM μ A S' hS K' hp hX x).1
  have hP b : Grass (P b) := priorigrass (fun b=> Grass.list (s:=range (b+2+1)) (F:=fun r=> stanza (S' b r) c) fun r _=> Grass.base (Hemi.pos (recital _ _))) b
  have he:= dock_wins hX hM μ x (wheat _ _ (fun b=> dryL i (V b) _) hP j) (windows τ j) (fun v ht=> h₃ v j ht)
  calc
    _ = emitter τ (K'.acts c) H U' j x := he.trans (by simp [Quire.emitter,billow,furnace,Finset.sum_apply,U',P,H])
    _ = _ := by
      rw [show emitter τ (K'.acts c) H U'=billow Q (cloud (K'.acts c) H 1) from h₂,billow,Finset.sum_apply]; refine sum_congr rfl fun b _=> congr_arg (Q b.1 x * ·) (hz _)
end weights

section wakes
variable (G) (S : StepData c f) {U : BoardU D R G} {o : Site c} {φ : Exam D}

abbrev valve (U : BoardU D R G) (S : StepData c f) (φ : Exam D) (h τ : ℕ) (o : Site c) : Reel (Psalm (Co c (Park G S.patch.L))) := fun e=>
    large o (τ+e) (fun r=> plug φ R ∘ cream h U S.patch.L e r)
-- any conjoined point rooted mark. single-tag here.
lemma onValve (P : Patch) (T : KernelChoices)(w : Train P.J) (hd : f.val=c.val*P.L.val) (O : Matrix (Body 1 f) (Body 1 c) ℝ)(o : Site c)
    (M : FreeResolvent.FaceRow) (hX : Inputs (linked P T c f hd) O ((pink T.penalty w).acts f) (M.acts c))
    (ν : G.ColorIndex) (D' : ChartRatio G) (X : Repeated P.L)
    (A : Air G) (hA:Gets A) (hp:P.Branches T G) (φ : Exam D) (hR : 1/2≤R) (hB : Fits τ U)
    (he : ∀ j r,Pens (U j r)) (h : ℕ) :
    let S:= linked P T c f hd
    let B:= awakening ν P D' T.penalty A
    let F:=X.forest S.ratio
    let Q:= coarseMean G X T w
    let K:= conditionalCov G X T w
    ∀ (v : Link G c),
    let W:= lodgeP G S.ratio (riseM S G F O *ᵥ v) v
    let L := leaned (forest_precision G T w c f hd hp F) (snow G F) (chargeS S F G) W
    let H := expEra (surge S G A ν D')
    let V := valve G U S φ h τ o
    let Y e:= large o (τ+e) (fun r=> plug φ R ∘ filop K Q B (some c) τ h U e r)
    ∀ j,L (billow V H j)=∑ a∈wheel j,Y a.1 v*L (H a.2) := by
  intro S B F Q K v W L H V Y j
  have hW := Gets_awake P D' T ν hA; have hm: Whole K:= (conditional_truth G X T w hp).1
  have ht: Whole Q:= (hm.prod ((probe_recites G P T).1.flipped)).weight _
  have hδ := P.odd_side -- ratios defeq
  have h' := forest_precision G T w c f hd hp F
  let I i r:= plug φ R ∘ cream h U S.patch.L i r
  obtain ⟨h₁,h₂⟩:= creamy h P.L hB he hR hδ
  have hC : Fits τ I := fun i r ph => h₁ i r (fun H=> ph (by unfold I; rw [show cream h U S.patch.L i r=0 from H]; ext; simp))
  have hx := consumes (V:=I) h' (snow G F) (veiled_whole hm) (chargeS S F G) (people P T X w hp hd) hW (fun i k=> Tidy.map _ (h₂ i k)) hC o W j
  refine Eq.trans hx (sum_congr rfl fun a _=>?_)
  apply congr_arg (· * leaned _ _ _ W (H a.2))
  change _=Y a.1 v
  unfold Y; rw [projected_out (K:=K) (Q:=Q) hδ hR hB he hm ht hW.1 (fun i j=> (hW.2 i j).1) φ]; rw [show (scan Q).acts c *ᵥ v=W from tree_lodge G T hd hp v hX]

local notation "U_" j => (fun i k=> plug (Pages.roll (spinner j) (S.ratio.count.val:ℝ)⁻¹ φ) R ∘ U i k)
local notation "z_" j => (S.ratio.assemble (o,j))
def chapel (k : ℕ) (W : Site S.ratio.count → ℕ→Config G f→ℝ) (τ h : ℕ) (t : ℝ) (p : Config G f) :=
    ∑ i:Site S.ratio.count, ((S.ratio.count.val:ℝ)^h / Fintype.card (Site S.ratio.count)) * ∑ j∈range (k+τ+1), t^j*W i j p
lemma soaring (k τ h : ℕ)(W : Site S.ratio.count → ℕ→Config G f→ℝ) (hR : 1/2≤R) (hr : ∀ i j,Pens (U i j))
    (hX : ∀ (p:Site S.ratio.count) j,Cargo (z_ p) τ j (k+τ) (U_ p) (W p j)) (A : ℝ→ Alley G S.ratio)(hx : ContinuousAt A 0) :
    Fit (τ+(k+1)) (fun t=> chapel G S k W τ h t (input G f (fineL G S.ratio (t • A t)))) (fun t=> t^τ * year (fun e t=> valve G U S φ h τ o e (A t)) k t) := by
  let z:ℝ:=(S.ratio.count.val:ℝ)^h / Fintype.card (Site S.ratio.count)
  let Y:= fun t=> fineL G S.ratio (A t)
  let Q (p:Site S.ratio.count) t:=arco f (fun e=> large (z_ p) (τ+e) ((U_ p) e)) Y k t
  have he (p:Site S.ratio.count):= fileFit (W:= W p) (x:=fun t=> fineL G S.ratio (A t)) ((fineL G S.ratio).continuous.continuousAt.comp hx) (hX p)
  have hv (t : ℝ) (i' e : ℕ) : rootSong (plug φ R ∘ cream h U S.patch.L e i') c o (A t)=
      ∑ j:Site S.patch.L, z*rootSong ((U_ j) e i') f (z_ j) (Y t) := cream_present S.ratio (A t) o h e i' φ (hr _ _) hR S.patch.odd_side
  have hm t: t^τ * year (fun e (t:ℝ)=> valve G U S φ h τ o e (A t)) k t=∑ p:Site S.ratio.count,z*(t^τ*Q p t) := by
    simp only [Q,arco,year,valve,large, Finset.sum_apply]; simp_rw [smul_eq_mul,hv]; simp_rw [Finset.mul_sum]
    rw [sum_comm]; apply sum_congr rfl; intro i hi; rw [sum_comm]; apply sum_congr rfl; intro j _; apply sum_congr rfl; intro w _; ring_nf; rfl
  simp_rw [chapel,hm,map_smul]
  exact Fit.emp (s:=univ) (fun p (_:p∈(univ:Finset (Site S.ratio.count)))=> (he p).scale z)
end wakes
end YM.RG08.Loom
