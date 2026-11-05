import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Olive
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Inc
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Boulevard.Oro
import YM.RemainderComparison.Gear.Class

/-!
# Uncut ledge for the inherited income test

 Pull a raw rendering of the branch around the oriented test point with the
 input small only in this epoch. Gear, not just Blur.pay. When scattering on
 prime log inputs, the form has zero at origin. Use `Brush.even` rather than
 interpolating values to price ALL derivatives with the rescuing factor.
-/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.Gate
open Filter Function Lattice RG Pressure Pressure.Tube Pressure.Stores Work.E03 Work.F03 Exterior Wilson Push Push.AbsoluteSums Finset
open Precision Shell Channel Next.Fluctuations Bloch Laurent SliceRows Mask Coat SliceRows.DataKernel Metric
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical InnerProductSpace
open Brush Frond Gate Scroll Blaze RemainderComparison
variable {G : Gauge} {c f L : Side} {P:Teller G} {S:StepData c f} {T:Tube G S}

lemma stationery (P : Teller G) (L : Side) (j : ℕ) {V : ℝ→ℝ} (h : Gear G L (-(1/2)) V) :
    ∃ Q : ℝ→ℝ, Gear G L (-(1/2)) Q ∧ ∀ᶠ s in atTop,
    ∀ (c f : Side) (S : StepData c f) (T : Tube G S), Works P L s S T →
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U : E → Config G c) (x:E) (p : ℕ) (o : Site c),
    Mode U x j (V s) → p ≤ 32*radiusB s→ Clean (U x) s o (p+1) →
      ∃ (z : Site c→ G.El) (L : E→ Directions G c), Brush j (Q s) 1 L x ∧
        ∀ᶠ i in 𝓝 x, AgreeNear id o p (gauge z (U i)) (increment 1 (L i)) := by
  obtain ⟨C,r,hC,hr,hk⟩ := extend_interior G
  let F x := 32*radiusB x+1
  let u x := 16*(2*(F x:ℝ)+1)^5*(Fintype.card PlaqAxes:ℝ)*(2*Pressure.fiery G x L)
  let B x:= C* u x
  have hf : Reserve G L (fun x=>(F x:ℝ)):= Reserve.lag ..
  have he : Gear G L (-(1/2)) u := by
    unfold u; simpa only [zero_mul,zero_add] using! ((((((Gear.zero.mpr hf).mul_left 2).add (Gear.zero.mpr (Reserve.const 1))).pow 5).mul_left 16|>.mul_right (Fintype.card PlaqAxes:ℝ)).mul ((Gear.flame (G:=G) (L:=L)).mul_left 2))
  have hb:= he.mul_left C
  obtain ⟨J,d,hJ⟩:= cleanly G j 1 zero_lt_one
  obtain ⟨e,hR,hr'⟩:= PhysicalNext.Repeat.Boulevard.seek (G:=G) hJ.pos
  let D x:=(1+royalty G)*V x
  have hd := h.mul_left (1+royalty G)
  let K : ℝ := j.factorial*J; have hK:0≤K:=by have h:= hJ.value; unfold K; positivity
  refine ⟨fun s=> B s + K*D s,hb.add (hd.mul_left K),?_⟩
  filter_upwards [he.rate.below (by norm_num) _ hr, Delay.shift_pos G L, hb.rate.below (by norm_num) _ hR,
    hd.rate.below (by norm_num) 1 zero_lt_one, room G P L] with x hE hX hU hB ht c f S T hS E _ _ U X p o hv hp hw
  have hA:0≤u x:=by have h:0<Pressure.fiery G x L:= Work.E09.temp_pos hX; unfold u; positivity
  have hz:0 ≤ B x:= mul_nonneg hC.le hA; have he := ht c f S T hS
  obtain ⟨z,hV⟩ := Work.E08.axial_patch o (U X) p (p+1) le_rfl (by have hh := he.buys; omega) _ (show 0≤Pressure.temp x from by unfold Pressure.temp; positivity)
    (fun i hi j => hw.toll (b := (i,j)) hi)
  let g (x:E):=gauge z (U x); let L' (x:E) (j : Bond c) := if separation o j.1 ≤ p then G.plog (G.mat (g x j)) else 0
  have hb : ∀ i : Bond c, separation o i.1 ≤ p → G.chord (g X i)≤u x := by
    intro i hi; apply (hV i hi).trans
    unfold u; gcongr
    · unfold Pressure.temp; positivity
    · unfold F; omega
    simpa only [hS.length_eq] using! he.temperatures
  obtain ⟨b,hy,hx⟩ := hk id o p (g X) _ hA ((le_abs_self _).trans hE) hb
  have hy (i:Bond c)(hi:separation o i.1 ≤ p): ‖G.plog (G.mat (g X i))‖≤ B x∧ ‖G.mat (g X i)-1‖≤d :=by
    let y:=b (pole i); have hs: g X i=G.lieExp y:=by rw [show g X i=_ from hx i hi]; unfold represent increment; rw [Pi.one_apply,mul_one]; rfl
    have hb' : ‖y‖≤ B x:= (norm_le_pi_norm _ _).trans hy
    obtain ⟨hy,he⟩:= hr' y (hb'.trans ((le_abs_self _).trans hU)); rw [hs,hy]; exact ⟨hb',he⟩
  have ht := soak hv z
  have hF:0≤D x:= by have h:=royalty_ge G; have hh:=hv.pos; unfold D; positivity
  have hh i : Brush j (B x+K*D x) 1 (fun y=> L' y i) X := by
    unfold L'; split_ifs with hm
    · exact shrinker ((ht.atLink i).pine (hJ.sound _ (hy _ hm).2)) (hy i hm).1 ((le_abs_self _).trans hB)
    exact (certified (show (0:ℝ)≤1 from zero_le_one) (0:G.Color)).climb (by rw [norm_zero]; positivity) le_rfl
  refine ⟨z,L',Brush.fold zero_le_one (by positivity) hh,?_⟩
  let e':= univ.filter fun i:Bond c=> separation o i.1≤p
  have hb i (h:i∈e'):∀ᶠ y in 𝓝 X,g y i=increment 1 (L' y) i:=by
    have hi := (mem_filter.mp h).2
    have hz : ‖G.mat (g X i)-1‖ < 2*d := lt_of_le_of_lt (hy i hi).2 (by have h:=hJ.pos; linarith)
    have he : ContinuousAt (fun y : E=> ‖G.mat (g y i)-1‖) X := ((ht.atLink i).smooth.continuousAt.sub_const (1:G.Mat)).norm
    filter_upwards [he (gt_mem_nhds hz)] with y hy; unfold increment L'; rw [if_pos hi,hJ.inverse _ hy,Pi.one_apply,mul_one]
  filter_upwards [(Finset.eventually_all _).2 hb] with y hz i hi; exact hz i (mem_filter.mpr ⟨mem_univ _,hi⟩)

lemma no_write (h : P.Funds S T) (k:S.Choices) (p : Rod c f) (s : ℝ) : Scroll.freely T s 1 k p=0 :=by
  have hh {c : Side}(S:PathData G)(p:Clip)(R M)(a:Twin c): plotted S p R M (1: Config G c) a=0:=by
    have he (n : ℕ) : shortenTerm S R M (1:Config G c) a.1 n=0 := by
      unfold shortenTerm; split
      next hv => simp [PathData.ellTerms, Work.F03.atSite_path,faceValue, SliceRows.trivial]
      exact rfl
    unfold plotted; split
    next => simp only [shorten,he,tsum_zero]
    simp [shoot,faceValue, SliceRows.trivial]
  unfold Scroll.freely baseStroke entryCost visual; rw [replica_one]
  have he (u : Twin c) : T.Xn (till s) (1 : Config G c) u=0 := hh ..
  rw [show S.prediction 1 k=(1:Config G c) from funext fun i=> Push.settled S (SectorMeasure.funds_branch h) i k]
  rcases p with i|i
  · simp only [Sum.elim,Tube.Xf,hh,canopyF,zip,he,map_zero,sum_const_zero,sub_zero]
  simp only [Sum.elim,canopyI,zip,Tube.Z,he,Pi.one_apply,inv_one,mul_one,G.curvature_unit,smul_zero,map_zero,sum_const_zero,sub_zero]
lemma appraise (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) :
    ∃ (R:ℝ), 0<R ∧ ∃ (A : ℝ→ℝ), R≤1 ∧ Reserve G L A ∧ ∀ x (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D → Works P L x S T→
        ∀ (k : S.Choices) (p : Rod c f), ∀ z : ZipP G c f, ‖z‖≤R → Brush j (A x) 1 (fun (v:ZipP G c f)=> Scroll.freely T x (increment 1 v.1) k p) z := by
  obtain ⟨r,v,hr,h1,hv,h⟩:= dressed P D hD j
  let f x:= shadowL P+maxima P L (till x); let g x:= hikeZ G v (till x) (dimLift P (till x) v)
  have ht:=Reserve.tillP (G:=G) (L:=L)
  have hf : Reserve G L f := (Reserve.const _).add (((Reserve.ball (till ·) ht).mul (Reserve.const _)).mul (Reserve.const _))
  have hg : Reserve G L g := by
    unfold g hikeZ dimLift
    have h (c:ℝ):= Reserve.const (G:=G) (L:=L) c
    exact ((((h 2).mul ht).mul (h _)).mul (h _)).add (((((h 4).add ((h 2).mul ht)).mul (h _)).add (h _)).add (h _))
  refine ⟨r,hr,_,h1,(hf.mul (((Reserve.const 1).add hg).pow j)),fun x c f S T hs ht k p x' hX=>?_⟩
  obtain ⟨h₁,-,-,-,h₂⟩:= h _ _ S T ht.funds hs x' hX k
  exact (grove ht.funds ht.length_eq h₁ k h₂ p _).trim
lemma charters (P : Teller G) (L : Side) (D : Patch) (hD : D.Branches P.bind G) (j : ℕ) {v : ℝ→ℝ}
    (h : Gear G L (-(1/2)) v) : ∃ F : ℝ→ℝ, Gear G L (-(1/2)) F ∧ ∀ᶠ x in atTop,
    ∀ (c f:Side) (S : StepData c f) (T : Tube G S), S.patch=D→ Works P L x S T→ ∀ (k:S.Choices) (p:Rod c f)
    (E:Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (U:E→ Config G c) (z:E), Mode U z j (v x)→
      Clean (U z) x (focus S p) (radiusB x) → Brush j (F x) 1 (fun t=> Scroll.freely T x (U t) k p) z := by
  obtain ⟨R,hr,A,hR,hv,hP⟩:= appraise P L D hD (j+1)
  obtain ⟨F,hF,hG⟩:= stationery P L j h
  let B x:= F x+F x
  refine ⟨fun x=> (A x+j.factorial*A x)*B x,(by simpa only [B,zero_add] using (Gear.zero.mpr (hv.add ((Reserve.const (j.factorial:ℝ)).mul hv))).mul (hF.add hF)),?_⟩
  filter_upwards [hG,(hF.add hF).rate.below (by norm_num) R hr,room G P L] with
    x H hx hf c f S T hs hh k p E _ _ U z hU hE
  have hp:=hf c f S T hh; have hX:=hp.sight
  let W (x' : Config G c) := Scroll.freely T x x' k p
  let g (v:ZipP G c f):= W (increment 1 v.1)
  obtain ⟨d,b,hθ,hA⟩:= H c f S T hh _ U z (radiusB x/4) _ hU (by omega) (hE.shrink (by rw [separation_self]; omega))
  let V' i := (b i,(0:Directions G f)); have ht:=hθ.nonneg
  have hY : Brush j (B x) 1 V' z:=Brush.pair hθ ((Brush.certified zero_le_one _).climb (show ‖(0:Directions G f)‖ ≤ F x by rw [norm_zero]; exact ht) le_rfl)
  let O:=Metric.closedBall (0: ZipP G c f) R
  have he' i (hi:i∈O):Brush (j+1) (A x) 1 g i:= hP x _ _ _ _ hs hh k p _ (mem_closedBall_zero_iff.mp hi)
  have h0:(0: ZipP G c f)∈ O:=mem_closedBall_self hr.le
  have hF':V' z∈O:= mem_closedBall_zero_iff.mpr (hY.bound.trans ((le_abs_self _).trans hx))
  have hm:‖g (V' z)‖≤ A x* B x:=by
    have hf:(∀ i∈ O, DifferentiableAt ℝ g i):=fun i hi=> (he' i hi).smooth.differentiableAt (by exact_mod_cast Nat.succ_ne_zero j)
    have hu i (h:i∈ O) : ‖fderiv ℝ g i‖≤ A x := (norm_iteratedFDeriv_one _).symm.trans_le ((offer.1 (he' _ h)).2 1 (by omega))
    have hh := Convex.norm_image_sub_le_of_norm_fderiv_le hf hu (convex_closedBall _ _) h0 hF'
    rw [show g 0=0 from (by unfold g W; dsimp only [Prod.fst_zero]; simp only [Work.G07.at_zero_increment,no_write (k:=k) (s:=x) ‹Works _ _ _ _ _›.funds p]),sub_zero,sub_zero] at hh
    exact hh.trans (mul_le_mul_of_nonneg_left hY.bound (he' _ h0).nonneg)
  let F' := (G.adjoint (d (focus S p))⁻¹).toContinuousLinearMap
  have hg := (hY.even ((he' _ hF').smaller (show j ≤ j+1 by omega)) (((le_abs_self _).trans hx).trans hR) (he' _ h0).nonneg hm).report F' (v:=1) (ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun x=> by
     rw [one_mul]; exact (G.norm_adjoint _ _).le)); rw [one_mul] at hg
  apply hg.shimmy
  filter_upwards [hA] with i hi
  have hv : W (gauge d (U i))=g (V' i) := by unfold W g W freely baseStroke; dsimp only [V']; rw [entry_stencil hp _ _ _ _ k p (replica_near hi) hi, shoreVisa hp p hi]
  change W _=G.adjoint _ (g (V' i)); rw [← hv]; unfold W
  rw [peony d hh.funds,← G.adjoint_mul, inv_mul_cancel, G.adjoint_one]
end YM.ConnectedActivityE6.Blaze.Gate
