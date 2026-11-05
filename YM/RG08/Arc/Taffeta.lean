import YM.RG08.Arc.Pleats

/-! # Taffeta function in real domain with literal Hess gap augmented
for proof path variable by one. No inference of physical-domain absence
of other saddles. -/
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
local notation "Q" => YM.RG08.quad G (YM.RG08.hessian M)
local notation "W" => regal S G T U v κ n V Q
local notation "Δ" => treeMatrix G S T K

-- same across gradient zero-modes; leading quadratic
lemma ray_straights (h : ContDiffAt ℝ ω v 0) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i))
    (hF : Decked F) (hA : Halt F) (hX : Whole K) (hR : Whole M) (hK : ∀ m,(K.acts m).IsSymm) (hM : ∀ m,(M.acts m).IsSymm)
    (hU : Inputs S U (K.acts f) (M.acts c)) (x : A) :
    Fit (n+2+1) (fun t=> W (t•plates G T.Free (maplit G T x)))
      (fun t=> t^2*(x ⬝ᵥ (Δ *ᵥ x)/2 + 1 + year (fun e t=> billingQ S i F e (heated S G T U v t x)) n t)) := by
  let P := plates G T.Free (maplit G T x); let U' := fun t=> heated S G T U v t x; let D := fun t:ℝ=>t^2*(1-stanza Q c (v t))
  have hs (t : ℝ) : (t•P).2=t := mul_one t
  have hJ := evaluateQ S n i κ hp K hX hK V he hF hA _ (heat_lamp S G T U v h x).continuousAt
  have h' := hJ.pair (Fit.same D _)
  have hx : (fun t=> W (t•P))=(fun t=> laboratory S κ n V t (input G c (coarseL G S.ratio (t • U' t))) (input G f (fineL G S.ratio (t • U' t))))+D := by
    funext t; rw [regal, hs, show chic S G T U v (t•P)=t•U' t from chic_ray ..]; rfl
  change Fit _ (fun t=> W (t•P)) _
  rw [hx]; refine h'.join (Fit.supply (Eventually.of_forall fun t=> ?_) _)
  rw [Pi.add_apply]; unfold D
  rw [heat_pose,lodge_f,lodge_c, bed_gather S hU (hK f), (price_stanza G hR hM c).2.2]; ring

-- Stationarity follows from ray equality on every HEIGHT 1 plane. Extend by homogeneity/density to all pairs.
include i
private lemma spark_kin (h : ContDiffAt ℝ ω v 0) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i))
    (hF : Decked F) (hA : Halt F) (hX : Whole K) (hR : Whole M) (hK : ∀ m,(K.acts m).IsSymm) (hM : ∀ m,(M.acts m).IsSymm)
    (hU : Inputs S U (K.acts f) (M.acts c)) (j : ℕ) (x : A) (hj : j≤2) :
    jet W j (plates G T.Free (maplit G T x))= if j=2 then x⬝ᵥ (Δ *ᵥ x)/2+1 else 0 := by
  let P:= fun e t=> billingQ S i F e (heated S G T U v t x)
  let p:=plates G T.Free (maplit G T x); let D := x ⬝ᵥ (Δ *ᵥ x)/2+1
  have hb e : Bill 0 (P e) := by
    have hv := heat_lamp S G T U v h x |>.continuousAt; have hs : ContinuousAt (P e) 0 := by
      unfold P billingQ; split_ifs with hh
      · exact continuousAt_const
      exact ((show Grass (grand (e+2) (F e) f) from Grass.list (fun i _=> Grass.base (Hemi.pos (recital (F e i) f)))).smooth.continuous.continuousAt.comp ((fineL G _).continuous.continuousAt.comp hv)).add ((stanza_smooth ..).continuous.continuousAt.comp hv)
    exact life_price (hs.mono_left nhdsWithin_le_nhds) -- ContinuousAt
  let L' : ℝ→ℝ := fun t=>t^2*D
  have ht : Fit 3 (fun t=>t^2*(D+year P n t)) L' := by
    unfold Fit L'; rw [show (fun t:ℝ=>t^2*(D + year P n t)) -(fun t:ℝ=> t^2*D)=(fun t:ℝ=> t^2 * year P n t) from funext fun t=>by simp [mul_add]]; exact bill_mul (k:=2) (j:=1) (ruler 2 _ le_rfl) (year_earns hb n (funext fun t=>by simp [P,billingQ]))
  have hs : ContDiffAt ℝ ∞ W 0 := regal_fit S G T U v κ n V F K i Q h hp he |>.of_le le_top
  exact aspiredV (((ray_straights S G T U v κ n V F K M i h hp he hF hA hX hR hK hM hU x).lower (by omega : 3 ≤ n+2+1)).join ht) (directions hs p) (Aspiration.single D 2) hj
lemma day_station (h : ContDiffAt ℝ ω v 0) (hp : S.patch.Branches S.kernel G) (he : ∀ i,Caper (quad G (YM.RG08.hessian K)) F n i (V i))
    (hF : Decked F) (hA : Halt F) (hX : Whole K) (hR : Whole M) (hK : ∀ m,(K.acts m).IsSymm) (hM : ∀ m,(M.acts m).IsSymm)
    (hU : Inputs S U (K.acts f) (M.acts c)) (hΔ : (Δ).PosDef) :
    PertExtension.Series.Radial.Stationary W ∧ ∃ a>0,∀ p:Z,a*‖p‖^2≤jet W 2 p := by
  let R := maplit G T
  have hj:= spark_kin S G T U v κ n V F K M i h hp he hF hA hX hR hK hM hU
  have hp' (j : ℕ) (x : A) (z : ℝ) (hr : j≤2) : jet W j (R x,z)=if j=2 then x ⬝ᵥ (Δ *ᵥ x)/2+z^2 else 0 := by
    have hs (t : ℝ) (h : t≠0) : jet W j (R x,t)=if j=2 then x ⬝ᵥ (Δ *ᵥ x)/2+t^2 else 0 := by
      rw [show ((R x,t):Z)= t•plates G T.Free (R (t⁻¹ • x)) by simp [plates,map_smul,smul_inv_smul₀ h], jet_smul]; rw [show jet W j (plates G _ _)=_ from hj j _ hr]; split
      · rename_i eq; rw [eq,Matrix.mulVec_smul, smul_dotProduct,dotProduct_smul]; simp only [smul_eq_mul]; field_simp
      rename_i e; rw [mul_zero]
    by_cases H : z=0; swap; · exact hs z H
    subst z
    let f' := fun t : ℝ=>jet W j (R x,t)
    let g' := fun t:ℝ=> if j=2 then x ⬝ᵥ (Δ *ᵥ x)/2+t^2 else 0
    have hl : Continuous f' := (PertExtension.Series.Radial.Smooth.continuousJet ..).comp (continuous_const.prodMk continuous_id)
    have hg : Continuous g' := by unfold g'; split <;> fun_prop
    exact tendsto_nhds_unique ((hl.continuousAt (x:=0)).mono_left nhdsWithin_le_nhds) (((hg.continuousAt (x:=0)).mono_left nhdsWithin_le_nhds).congr' (eventually_pos.mono fun t ht=> (hs t ht.ne').symm))
  constructor
  · refine ⟨((regal_fit S G T U v κ n V F K i Q h hp he).of_le le_top), ?_, fun x=>?_⟩
    · exact (jet_zero W _).symm.trans (hj 0 0 (by omega)) -- δ?
    obtain ⟨x,z⟩:= x; obtain ⟨y,rfl⟩:=R.surjective x; rw [hp' 1 _ _ (by omega),if_neg (by omega)]
  apply quadratic_min; intro p hP
  obtain ⟨x,z⟩:=p; obtain ⟨y,rfl⟩:=R.surjective x
  rw [hp' 2 _ _ le_rfl,if_pos rfl]
  by_cases hh : y=0
  · rw [hh,map_zero] at hP; subst y; have hn : z≠0:= fun eq=> hP (by rw [eq]; rfl); rw [Matrix.mulVec_zero,dotProduct_zero,_root_.zero_div,zero_add]; exact sq_pos_of_ne_zero hn
  exact add_pos_of_pos_of_nonneg (by exact div_pos (hΔ.dotProduct_mulVec_pos hh) (by norm_num)) (sq_nonneg _)
end YM.RG08.Reflect
