import YM.Further.CORRECTED_LIFT_COEFFICIENTS.Dollars
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Pose
import YM.PhysicalNext.PHYSICAL_GUARD_7F546.Continuation.Scales
import YM.PhysicalNext.WEIGHTED_GAUSSIAN_MARGINAL_LIMIT_45C.Venue.Chips

/-!
# Focusing rows on a genuine single pose

Uses both announcements of 45C's `aperture` on every readable
address at that pose. `StrongScope.sight`: about landmark log means
(even for arbitrary Y on Frozen), and actual masked Gaussian
curl covView versus the forest-independent free comparator. This doesn't
say that nonlinear curvature reads are given by this linear law. See later
Rail etc. for where we fit on those arguments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure Precision RG RG.Supply Laurent Bloch Matrix Finset Filter
     Next.Rank Tapes Perch Paint Spindle 
    WeightedGaussianMarginal45C.Venue PhysicalGuard7f546.Curved
    AnalyticBridge.LocalGaussianLaws Work.F08 FreeResolvent Exterior Remote Local Lift Tree Bid
    Function Assembly Current Next.SectorChange Next.SectorChange.Rows Next.Fluctuations
    Push.SectorMeasure Pressure.Stores Gaussian Wisps
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f}

structure StrongScope (P : Patch) (T : Teller G) (B : ℝ) (x : ℝ) : Prop where
  cash : 1≤B
  ribbon : ∀ {c f : Side} (S : StepData c f) (H : Tube G S), S.patch=P → T.Funds S H → Larger (G:=G) S → 100*(1+radiusB (retime x))≤c.val → ∀ (A : Stores S) (F : Forest S.ratio) (k : S.Choices) V, A.flags=RG.flags (temp (retime x)) V →
    ∀ s, let Q := palette H A F k (retime x) V s; Q.PosDef ∧ ∀ i j, |Q i j|≤B
  sight : ∀ {c f : Side} (S : StepData c f) (H : Tube G S), S.patch=P → T.Funds S H → Larger (G:=G) S → 100*(1+radiusB (retime x))≤c.val →
    ∀ (P L : Bed) (a m e k : ℝ), 0<a → 0<m → Floor P H.high f a e → Floor L H.low c m k → Attached P H.up → Sworn P f G →
    Towers.Diagonal S P L H.R → Booth T S H →
    ∀ W (A : Stores S) o V v, Pose A o W x V v → ∀ (F : Forest S.ratio) (k : S.Choices) (q : Chi) (d : ℝ) (s : Geometry) (Y : LinkArray G (Frozen A (retime x) F)),
      let V' := spine V o; let M:=portrait H A F k (retime x) V' s q d Y; let Q:= palette H A F k (retime x) V' s
      (∀ j, separation o (front A F j)+walls x≤W → |M j - portrait_head H F v (loadLink A F (retime x) j)|≤x^(-(7/8):ℝ)) ∧
      ∀ (i j : FreeResolvent.Slot G f 2), separation o (S.ratio.parent i.1)+walls x+1 ≤ W → separation o (S.ratio.parent j.1)+walls x+1 ≤ W →
        |(SectorTools.PhysicalGaussianSwitch.covView (dKeys A F (retime x)) Q) i j - tensor G (fConditional S P L H.R) i j| ≤ x^(-(1/8):ℝ)

-- purchased after patch. ε can then take x^(-1/8) before comparing
-- to the short stencil.
lemma scopes (P : Patch) (Pt : Teller G) (hP : P.Branches Pt.bind G) : ∃ E : ℝ, 1 ≤ E ∧ ∀ᶠ x in atTop, StrongScope P Pt E x := by
  obtain ⟨p,s,M,C,E',q,hp,hs,hM,hC,hE,hq,H'⟩ := AnalyticBridge.LocalGaussianLaws.quote G P Pt hP
  obtain ⟨u,η,K,Y,E,hu,hK,hY,hL,hη,H⟩ := freeHead G P Pt.bind Pt.top.clip Pt.top.width_pos Pt.top.paths_pos.le
  let U := curlTariff G P 0
  have hz : 0≤U^2*(K+1) := by have hh:=zero_le_one.trans hK; positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [burst_limit,eventually_gt_atTop (0:ℝ),tall_limit.eventually H',tall_limit.eventually H, tall_limit.eventually (Extra.Iteration.Scales.first E (1/4) hL),
    tall_limit.eventually (PhysicalGuard7f546.Curved.const_allow hz (show -(1/4:ℝ)< -(1/8:ℝ) by norm_num)),
    tall_limit.eventually (WeightedGaussianMarginal45C.Venue.aperture G P Pt hP 0 1 le_rfl)] with x hx hx0 hC' hK' ht' he h
  let B := (retime x)^(-(1/4):ℝ); let b:= radiusB (retime x)
  have hB : 0≤B := Real.rpow_nonneg (hx0.le.trans hx.1) _
  refine ⟨hC, ?_,?_⟩
  · intro c f S T ha hv hl hy A F k V hA s' Q
    obtain ⟨hl,hL'⟩:= hC'.2 S T ha hy hv A F k V hA
    have hh : Closes (native c) (front A F) (Rows.gram T (retime x) V k (shots S (retime x)) A F) (sectorW G S (retime x) A F s') s M p C (E'*Real.exp (-s*b)) q := by cases s'; exact hl; exact hL'
    exact ⟨hh.cloud,fun i j => entry (show (native c).Schur _ _ _ _ Q from hh.compares.1) hs.le i j⟩
  intro c f S T hP hT hS ht P₁ L a m e l ha hm hH hB' hh hs' hw hy W A o V v hV F k q' d g Y V' μ Q
  have ht0 : 0 ≤ clearanceFare (retime x) := by linarith only [hV.worth,norm_nonneg v]
  let Z:=bareStores S; let X:=opened G S (retime x) Z F (bare_is_Clear S (retime x) F); let H:=panoramic T A F k (retime x) V' g; let H':=panoramic T Z F k (retime x) 1 g
  have hi (j) (hr : separation o (front A F j)+walls x≤W) :
      |μ j - portrait_head T F v (loadLink A F (retime x) j)| ≤ x^(-(7/8):ℝ) ∧ ∀ i : In (retime x) A F (G:=G), |H i j-H' (X (loadLink A F (retime x) i)) (X (loadLink A F (retime x) j))| ≤ B := by
    obtain ⟨h0,h1,h2⟩:=hV.center _ hr
    have he := h S T hP hy hS ht A (front A F j) h0 V' (by simp [V',spine,gauge_flags,hV.tolls]) v h1
      (by linarith only [hV.worth,ht0]) (by rw [one_mul]; exact h2) F k q' d g Y j (by simp)
    exact ⟨he.1.trans (Real.rpow_le_rpow_of_nonpos hx0 hx.1 (by norm_num)), he.2⟩
  refine ⟨fun i hv=> (hi i hv).1,fun i j hK0 hR => ?_⟩
  let F0:= plane S F (G:=G); let R := treeInverse G S F P₁.metric 0; let J:= mirror (H'.submatrix X X)
  let Z:=F0*J*F0.transpose; let K':=tensor G (fConditional S P₁ L T.R)
  have ph : K'=F0*R*F0.transpose := Eq.symm (cutHead S F P₁ hS hH ha T.R hB' hm hw)
  have hc (i : Remote.tileP (G:=G) (f:=f)) : ∑ j, |F0 i j|≤U := by
    unfold U; rw [← hP]; simpa only [Cost.weight_zero,one_mul] using (plane_price S F 0 le_rfl).rows.bound i
  let k₀:=loadLink A F (retime x) (G:=G)
  have hW (i : FreeResolvent.Slot G f 2) (j' : FreeResolvent.Active G F)
      (hh : separation o (seat S 2 i)+walls x+1 ≤ W) (hg : plane S F i j'≠0) :
        separation o (theta S.ratio F j')+walls x≤W := by
    have he := (separation_triangle o (seat S 2 i) (theta S.ratio F j')).trans (Nat.add_le_add_left (onTurn S F i j' hg) _); omega
  have hg (j' : FreeResolvent.Active G F) (h : separation o (theta S.ratio F j')+walls x≤W) : j'∈Set.range k₀ :=
    stationId A F (hV.center _ h).1 j' (by simp)
  have h₁ : |(SectorTools.PhysicalGaussianSwitch.covView (dKeys A F (retime x)) Q) i j-Z i j|≤U^2*B := by
    refine sandwich Q J k₀ k₀.injective F0 i j (fun j' h => hg j' (h.elim (hW i j' hK0) (hW j j' hR))) B U hB (hc _) (hc _) (fun a d hA hD =>?_)
    have ht := half_keep ((hi d (hW j (k₀ d) hR hD)).2 a) ((hi a (hW i (k₀ a) hK0 hA)).2 d)
    apply Eq.trans_le _ ht
    change |(1/2:ℝ)*(H a d+H d a)-1/2*(H' (X (k₀ a)) (X (k₀ d))+H' (X (k₀ d)) (X (k₀ a)))|=_
    congr 1; dsimp only [k₀]; ring
  obtain ⟨Λ,N,hY,hx'⟩ := hT.feeds
  obtain ⟨_,hF⟩:= hK'.2 S T hP hT.knobs hS hT.high Λ hY F k _ g (bare_is_Clear S (retime x) F) P₁ hh (hT.high ▸ hH.roots) hs'
  let A0:=K*Real.exp (-E*b)
  have hv : 0≤ K := zero_le_one.trans hK
  have hh : (native c).Schur (seat S 2 (G:=G)) (seat S 2 (G:=G)) 0 (U*A0*U) (Z-K') := by
    rw [ph]; unfold Z; rw [← Matrix.sub_mul,← Matrix.mul_sub]; unfold U; rw [← hP]
    apply plane_bill _ _ _ le_rfl (show 0≤A0 from mul_nonneg hv (Real.exp_pos _).le)
    rw [show R=(treeMatrix G S F P₁.metric)⁻¹ from by unfold R treeInverse resolve; rw [zero_smul,add_zero]]
    exact hF.cov.mono hu.le le_rfl
  have h₂ : |Z i j-K' i j|≤ U^2*(K*B) := by
    apply (entry hh (by norm_num) i j).trans
    exact (by nlinarith only [mul_le_mul_of_nonneg_left (show A0≤K*B from mul_le_mul_of_nonneg_left ht' hv) (sq_nonneg U)])
  apply le_trans _ (he.trans (Real.rpow_le_rpow_of_nonpos hx0 hx.1 (by norm_num)))
  refine (abs_sub_le _ (Z i j) _).trans ((add_le_add h₁ h₂).trans_eq ?_)
  unfold U B; ring
end YM.PhysicalNext.InteractingRank
