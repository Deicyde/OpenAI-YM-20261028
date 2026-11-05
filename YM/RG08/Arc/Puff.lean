import YM.RG08.Arc.Taffeta
/-! # Haar ratio curvature and field-independent Gaussian factors, finite test
One block. Positive recurrent coefficients. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Reflect
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {c f m : Side} (S : StepData c f) (G : Gauge) (T : Forest S.ratio)
variable (U : Matrix (Body 1 f) (Body 1 c) ℝ) (v : ℝ→ Link G c)
local notation "A" => FreeResolvent.Active G T →ℝ
local notation "L" => T.Free → G.Color
local notation "Z" => (T.Free → G.Color) × ℝ
variable (κ : S.Choices) (n : ℕ) (V : ℕ → Config G f → ℝ) (F : Air G) (K M : FreeResolvent.FaceRow) (i : G.ColorIndex)
variable (D : ChartRatio G) (hD : LocalRatio D)
local notation "Q" => YM.RG08.quad G (YM.RG08.hessian M)
local notation "W" => regal S G T U v κ n V Q
local notation "Δ" => treeMatrix G S T K

-- auxiliary path scalar factor chosen by regal step, no claim about zeroth UV factor.
def nibble (p : Z) := jacobian D (p.1+ shifting S G T U v p.2)
include hD
lemma nibble_meas (h : Measurable v) : Measurable (nibble S G T U v D) := (PertExtension.Chart.Ratio.jacobian_meas hD).comp (measurable_fst.add ((living_m S G T U v h).comp measurable_snd))
lemma nibble_fit (h : ContDiffAt ℝ ω v 0) : ContDiffAt ℝ ω (nibble S G T U v D) 0 := by
  apply (show ContDiffAt ℝ ω (jacobian D) (0+ shifting S G T U v (0:ℝ)) by rw [shift_zero,zero_add]; exact PertExtension.Chart.Ratio.jacobian_smooth hD).comp (f:=fun p : Z=> p.1+shifting S G T U v p.2) (0:Z) (contDiffAt_fst.add ((living_mean S G T U v h).comp (f:=Prod.snd) (0:Z) contDiffAt_snd))
lemma airing (F : Air G) (e) (h : Gets F) (t : Alley G S.ratio) :
    grand (e+2) (awakening i S.patch D S.kernel.penalty F e) c t = - billingQ S i F e t + jet (hatJ (f:=f) D) e (fineL G S.ratio t) := by
  -- rank e=0 excluded
  have hx := hD.anchored
  let A' := fun r=> gemL S.patch.L (F e r); let P r := blot i S.patch S.kernel.penalty r; let V' r:= gemL S.patch.L (brimJ i D r)
  have hh (r) : Tunable (A' r) := gem_tune _ _ (h.2 e r).1.1
  have hp (r) : Tunable (P r) := blot_sym ..
  have hi (r) : Tunable (V' r) := gem_tune _ _ (brim_tune i D r).1
  by_cases he:e=0
  · subst e; rw [billingQ,if_pos rfl, jet_zero,hatJ,Finset.sum_eq_zero (fun i _=> by rw [map_zero, Pi.zero_apply,hx]; exact Real.log_one),neg_zero,add_zero];
    have hv:= Gets_awake S.patch D S.kernel i h
    unfold grand; apply Eq.trans (congr_fun (sum_eq_zero ?_) t) (Pi.zero_apply ..)
    intro j hj; rw [not_ne_iff.mp (mt (hv.1 0 j) (fun H=> Nat.lt_irrefl _ H.1)),stanza_zero]; rfl
  -- RHS subtract
  have hg r : stanza (awakening i S.patch D S.kernel.penalty F e r) c t= -stanza (F e r) f (fineL G S.ratio t)-(if r=e+2 then stanza (P r) c t else 0)+(if r=e then stanza (V' r) c t else 0) := by
    let B : Shale (Park G S.patch.L) r := if r=e+2 then P r else 0; let D': Shale (Park G S.patch.L) r:= if r=e then V' r else 0
    have hV : Summable B:= by unfold B; split; exact (hp r).1; exact summable_zero
    have hP : Summable D':= by unfold D'; split; exact (hi r).1; exact summable_zero
    unfold awakening; simp only [show 0<e by omega,and_true];
    change stanza (-A' r-B+D') c t= _
    rw [stanza_add (show Summable (-A' r - B) from (hh r).1.neg.sub hV) hP, sub_eq_add_neg, stanza_add (show Summable (-A' r) from (hh r).1.neg) (show Summable (-B) from hV.neg),stanza_neg _ hV, stanza_neg _ (hh r).1]
    unfold D' B; simp only [Pi.add_apply,Pi.neg_apply]; rw [show stanza (A' r) c t=_ from gem_light _ (h.2 e r).1.1 S.ratio t]; split_ifs <;> simp [sub_eq_add_neg] <;> rfl
  unfold grand; erw [Finset.sum_apply]; simp_rw [hg, sum_add_distrib, sum_sub_distrib, Finset.sum_neg_distrib];
  have hP : e < e+2+1 := by omega
  simp only [Finset.sum_ite_eq',mem_range,Nat.lt_succ_self,hP, ↓reduceIte];
  have hb : stanza (V' e) c t=jet (hatJ (f:=f) D) e (fineL G S.ratio t) := by rw [jet_coefficient, ← (brim_good i hD f e).2]; exact gem_light _ (brim_tune ..).1 S.ratio t
  rw [hb, billingQ, if_neg he]; unfold grand P; rw [Finset.sum_apply]; abel

local notation "Ξ" => awakening i S.patch D S.kernel.penalty F
local notation "☼" => nibble S G T U v D
local notation "X'" => heated S G T U v
omit hD in
-- arc polynomial before exponential; useful also with single insertion
abbrev surge (e : ℕ) := grand (e+2) (Ξ e) c
omit hD in
def scout (t : ℝ)(x : A) := year (fun i' s=> expEra (surge S G F i D) i' (X' s x)) n t
-- band scalar `hatsScale` then exp(-1) both kept explicitly.
theorem apertures (h : ContDiffAt ℝ ω v 0) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i))
    (hF : Gets F) (hA : Halt F) (hX : Whole K) (hR : Whole M) (hK : ∀ m,(K.acts m).IsSymm) (hM : ∀ m,(M.acts m).IsSymm)
    (hU : Inputs S U (K.acts f) (M.acts c)) (x : A) (hΔ : (Δ).PosDef) :
    let R := plates G T.Free (maplit G T x)
    let H := (crownM hΔ).kern x
    Fit (n+1) (fun t=> PertExtension.Series.Radial.projection ☼ W t R) (fun t=> hatsScale S T D * Real.exp (-1) * scout S G T U v n F i D t x * H) := by
  intro R H
  let P:=crownM hΔ; let z:= x ⬝ᵥ (Δ *ᵥ x)/2+1
  let w (t : ℝ):=t•R -- annotate t
  let Y:= fun i' t=> billingQ S i F i' (X' t x)
  let Xi e t:= surge S G F i D e (X' t x)
  let ht' t:= hatJ D (t • fineL G S.ratio (X' t x)); let C t:= ht' t - W (t•R)/t^2; let Φ t := -z + year Xi n t
  have hg : Fit ((n+1)+2) (fun t=> W (t•R)) (fun t=> t^2*(z+year Y n t)) := ray_straights S G T U v κ n V F K M i h hp he hF.1 hA hX hR hK hM hU x
  let u:=fun t=> fineL G S.ratio (X' t x)
  have hX' := (heat_lamp S G T U v h x).continuousAt
  have hL : Bill 0 u:=life_price (((fineL G S.ratio).continuous.continuousAt.comp hX').tendsto.mono_left nhdsWithin_le_nhds)
  have hi : Fit (n+1) ht' (year (fun e t=>jet (hatJ (f:=f) D) e (u t)) n) := -- f shadow replace
    jet_path _ _ hL ((brim_good i hD _ n).1.contDiffAt.of_le le_top) _
  have hC : Fit (n+1) C Φ := by
    refine (hi.less (hg.shorten (k:=2))).join (Fit.supply (eventually_pos.mono fun t ht=> ?_) _)
    dsimp only [Pi.sub_apply]; unfold Φ year Xi Y
    rw [mul_div_cancel_left₀ _ (pow_pos ht 2).ne']; simp_rw [surge,airing S G i D hD F _ hF, smul_eq_mul,mul_add,sum_add_distrib,mul_neg,Finset.sum_neg_distrib];
    unfold u; abel
  have hu e : Grass (surge S G F i D e) := Grass.list (fun j _=> Grass.base (Hemi.pos (recital (Ξ e j) c)))
  have hy : ∀ i',Bill 0 (Xi i') := fun i'=> life_price (((hu i').smooth.continuous.continuousAt.comp hX').mono_left nhdsWithin_le_nhds)
  have hu0 : surge S G F i D 0=0 := by unfold surge grand; apply sum_eq_zero; intro j hj; rw [not_ne_iff.mp (mt ((Gets_awake S.patch D S.kernel i hF).1 0 j) (fun H=> Nat.lt_irrefl _ H.1)),stanza_zero]
  have hE := hC.elevate (bill_add (bill_const (-z)) (year_bills hy n))
  let B:=hatsScale S T D
  have hh (p : ℝ) : fineL G S.ratio (chic S G T U v (w p))= sprig S T G *ᵥ (maplit G T).symm ((w p).1+ shifting S G T U v (w p).2) := lodge_f ..
  have hf1 : Fit (n+1) (fun t=> PertExtension.Series.Radial.projection ☼ W t R) (B • (Real.exp∘Φ)) := by
    refine Fit.join (Fit.supply ?_ _) (hE.scale B)
    have hb : Tendsto (fun p=> w p) (𝓝 0) (𝓝 0) := by simpa [w] using! (show Continuous w from continuous_id.smul continuous_const).tendsto 0
    have hx : Tendsto (fun p=> (w p).1+shifting S G T U v (w p).2) (𝓝 0) (𝓝 0) := by
      have he' : Tendsto (shifting S G T U v) (𝓝 ((0:Z).2)) (𝓝 0) := by change Tendsto _ (𝓝 (0:ℝ)) _; simpa using (living_mean S G T U v h).continuousAt.tendsto
      exact (show (0:Z).1+0=0 by simp) ▸ (((continuous_fst.tendsto (0:Z)).comp hb).add (he'.comp ((continuous_snd.tendsto (0:Z)).comp hb)))
    filter_upwards [(hx.eventually (hats_restore S T hD)).filter_mono nhdsWithin_le_nhds] with t hv
    rw [projection_eq]; unfold nibble; rw [show jacobian D _=_ from hv]; change B*_ *_=B*Real.exp (C t); rw [mul_assoc, ←Real.exp_add]; congr 2
    unfold C ht'; erw [← hh t, show chic S G T U v (w t)=t • X' t x from chic_ray ..,map_smul (fineL G _)]; ring
  have ha : Fit (n+1) (Real.exp∘year Xi n) (fun t=>scout S G T U v n F i D t x) := year_aura (fun t=> aura_at (aura_starts hu0) (X' t x)) hy n
  have hH : H= Real.exp (1-z) := by unfold H z Law.kern; change Real.exp (-((_ *ᵥ x) ⬝ᵥ x) / 2)=_; rw [dotProduct_comm]; ring_nf
  refine hf1.join (Fit.join (Fit.supply ?_ _) (Fit.join (ha.scale (B*Real.exp (-1)*H)) (Fit.supply ?_ _)))
  · apply Eventually.of_forall; intro t
    change B * Real.exp (-z+ _)=(B * Real.exp (-1)* H)*_
    rw [Real.exp_add,hH,mul_assoc B, ← Real.exp_add (-1),show -(1:ℝ)+(1-z)= -z by ring]; rw [mul_assoc]; rfl
  apply Eventually.of_forall; intro t
  change B* Real.exp _*H *_=B*Real.exp _*_*_; ring
end YM.RG08.Reflect
