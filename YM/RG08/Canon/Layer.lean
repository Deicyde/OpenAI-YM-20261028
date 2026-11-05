import YM.RG08.Canon.Tokens
/-! # Canonical stationary grade identity on all finite periods.
Cubic/quartic no-cut and loop at same conditional Taylor point.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Canon
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f : Side} {G : Gauge} {S : StepData c f} {F : Forest S.ratio} {p : Clip} {R : PathData G} {σ M Λ : ℝ} {ρ : fieldDir G c 1 → AxisChart G F}
variable {η:ℝ} {t:S.Choices} {D : ChartRatio G}
variable {Q : Pot G 2} {W Z : Air G}

abbrev aureole (R : PathData G)(F : Forest S.ratio) (t : S.Choices) (p : Clip) (ρ : fieldDir G c 1→AxisChart G F)(D : ChartRatio G) (x:Link G c):= thermal F t p R ρ D (arm G c 1 x)-thermal F t p R ρ D 0
structure ShellC (F : Forest S.ratio) (p : Clip)(R:PathData G) (ρ:fieldDir G c 1→AxisChart G F)(D:ChartRatio G) (Q:Pot G 2) (Z:Air G):Prop where
   start : ∀ j,j ≤ 4 → ∀ t:S.Choices, Tensor.coeff (victory F t p R ρ) j 0=recital (sector Q Z 0 j) c
   fin t : ContDiffAt ℝ ω (aureole R F t p ρ D) 0
   rope : ∀ j,j ≤ 2→∀ t:S.Choices, Tensor.coeff (aureole R F t p ρ D) j 0=recital (sector Q Z 1 j) c

lemma fireflies {K B : FreeResolvent.FaceRow} {A : Matrix (Body 1 f) (Body 1 c) ℝ} {i:G.ColorIndex}{V:ℕ→Config G f→ℝ}
   (hc:Critical F p R ρ)(hl:PriceGap F p R η)(he : 0<η) (hd: LocalRatio D)(hw : R.Bounds p σ M Λ)(hx:S.patch.Branches S.kernel G)
    (hV : ∀ j,Caper (quad G (YM.RG08.hessian K)) W 2 j (V j)) (hR : Cask p R f (quad G (YM.RG08.hessian K)) W)
    (hW : Gets W)(hv : Halt W)(hK : Whole K)(hS : Whole B)(hC : ∀ m,(K.acts m).IsSymm)(hm : ∀ m,(B.acts m).IsSymm) (hs : Inputs S A (K.acts f) (B.acts c)) (hA : (treeMatrix G S F K).PosDef) (hG : G.Simple)
    (hy : ∀ w : Link G c,Aura (fun j=> leaned hA (snow G F) (chargeS S F G) (lodgeP G S.ratio (riseM S G F A *ᵥ w) w) (expEra (surge S G W i D) j)) (fun j=>-grand (j+2) (Z j) c w)) (hh : Decked Z ∧ ∀ i j,Tunable (Z i j)) : ShellC F p R ρ D (quad G (YM.RG08.hessian B)) Z := by
  let Q:=quad G (YM.RG08.hessian B)
  have hZ := (price_stanza G hS hm c).1
  let Y:= grand 4 (sector Q Z 0) c; let X:= grand 2 (sector Q Z 1) c
  have hF t : ContDiffAt ℝ ω (aureole R F t p ρ D) 0:= ((show ContDiffAt ℝ ω (thermal F t p R ρ D) (arm _ _ _ 0) from (map_zero (arm G c 1)).symm ▸ born hw hc hl he hd _).comp _ (arm G c 1).contDiff.contDiffAt).sub contDiffAt_const
  have ht (t:S.Choices) : (∀ i, i≤ 4 → Tensor.coeff (victory F t p R ρ) i 0= recital (sector Q Z 0 i) c) ∧
      (∀ i, i≤2 → Tensor.coeff (aureole R F t p ρ D) i 0=recital (sector Q Z 1 i) c) := by
    obtain ⟨L,hP,hD,hN,hE⟩:= revolves t hc hl he
    let P:Salvo t F R p ρ η L:=⟨hc,hl,he,hP,hD,hN,hE⟩
    let j:= arm G c 1
    have hz (x:Link G c) : Fit 5 (fun z:ℝ=> victory F t p R ρ (z•x)+z^2*aureole R F t p ρ D (z•x)) (fun z:ℝ=> Y (z•x)+z^2*X (z•x)) :=
      Fit.join (exalts x P hd hw hx hV hR hW hv hK hS hC hm hs hA hG hy) (Fit.supply (Eventually.of_forall fun z : ℝ=> token_change hh.1 Q z x) 5)
    have hj : ContDiffAt ℝ ω (victory F t p R ρ) 0:= (show ContDiffAt ℝ ω (fun u=> tested F t p R u (ρ u)) (j 0) from (map_zero j).symm ▸ score_slow P).comp _ j.contDiff.contDiffAt
    obtain ⟨hg,hT⟩:= stroke_sep _ _ _ _ hj (hF t) ((opus_whole (G:=G) _ 4 _).smooth.contDiffAt) ((opus_whole (G:=G) _ 2 _).smooth.contDiffAt) hz
    have hu (j k) := Tune_sector Z Q (fun i j=> (hh.2 i j)) hZ j k
    exact ⟨fun i hi => (hg i hi).trans (opus_jet _ (hu 0) _ _ _ hi),fun i hi=>(hT i hi).trans (opus_jet _ (hu 1) _ _ _ hi)⟩
  exact ⟨fun i hi t=> (ht t).1 i hi,hF,fun i hi t=> (ht t).2 i hi⟩

-- instance at any S with actual stamp. No En schedule premise needed for this; comparison consumer does need.
variable (P:Patch)(k:KernelChoices)(X:Repeated P.L)(w:Train P.J)(i:G.ColorIndex)
lemma staunch (u : f.val=c.val*P.L.val)
    (B : FreeResolvent.FaceRow) (hS : Whole B) (hm : ∀ i,(B.acts i).IsSymm)
    (A : Matrix (Body 1 f) (Body 1 c) ℝ) (hs : Inputs (linked P k c f u) A ((pink k.penalty w).acts f) (B.acts c)) (hx : P.Branches k G) (hd : LocalRatio D) (hG : G.Simple)
    (hW : Gets W) (hv : Halt W) (hF : Faithful (quad G (YM.RG08.hessian (pink k.penalty w))) W f)
    (hw : R.Bounds p σ M Λ)
    (hR : Cask p R f (quad G (YM.RG08.hessian (pink k.penalty w))) W) :
      let m := linked P k c f u; let F:= X.forest m.ratio
      ∀ ρ: fieldDir G c 1→ AxisChart G F,Critical F p R ρ → PriceGap (S:=m) F p R η → 0 < η →
        ShellC (S:=m) F p R ρ D (quad G (YM.RG08.hessian B)) (veil P k X w i D (some c) W) := by
  intro m F r hp hh he
  have hK : Whole (pink k.penalty w):=(heart_saves k.penalty k.penalty_pos P.order_cut (id : Train P.J→_)).1.whole w
  have hC (x) : ((pink k.penalty w).acts x).IsSymm:= (origins_psd _ k.penalty_pos P.order_cut w x).1.eq
  have hu := conditional_truth G X k w hx |>.1
  have hl:Whole (coarseMean G X k w):=(hu.prod (probe_recites G P k|>.1.flipped)).weight _
  obtain ⟨V,hV⟩:= costumed hF 2
  have hA : (treeMatrix G m F (pink k.penalty w)).PosDef:= forest_precision G k w c f u hx F
  apply fireflies (V:=V) hp hh he hd hw hx hV hR hW hv hK hS hC hm hs hA hG (fun x=> stationary_era G k i D P X w u B A hs hx x W hW (snow G F))
  exact exhale_deck hu hl (Gets_awake P D k i hW) (some c)
end YM.RG08.Canon
