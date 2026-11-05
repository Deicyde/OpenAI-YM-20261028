import YM.TraceExtension.Weir.Oolong
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Weir
open Function Filter Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Push.Uniform Det Lamp Analysis Finset
open Metric Filch Turret Shepherd AnalyticBridge VerifiedReset Extra.Iteration SectorAffine Offset Fen Kits Pills Loft Xo Zn StressFlux MeasureTheory Push.SectorMeasure
open PhysicalNext.JointLoad.Heir Next.Foundations Push.Local Swift WardBin WardBin.Lies WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Next.SectorChange
open Wicket Outer.Nodes
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{n:Side} {j:ℕ}
def wavesC (G:Gauge):= G.colorScale
private lemma layL(G:Gauge):∃ K:ℝ,1 ≤ K∧∀ u:G.Color,‖u‖ ≤ 1→G.chord (G.lieExp u) ≤ K*‖u‖:=by
   obtain ⟨T,hT,H⟩:= exists_allows (f:=G.mat ∘ G.lieExp) (s:=closedBall (0:G.Color) 1) (ProperSpace.isCompact_closedBall 0 1) (fun _ _=>G.exp_jet.contDiffAt) 1
   have hp:= G.colorScale_pos; refine ⟨max 1 (T/G.colorScale),le_max_left ..,fun u hu=> ?_⟩
   let f:= G.mat ∘ G.lieExp; have ht:= Convex.norm_image_sub_le_of_norm_fderiv_le (s:=closedBall (0:G.Color) 1) (f:=f) (C:=T) (𝕜:=ℝ) (fun x hx=> (H _ hx).analytic.differentiableAt (by simp)) (fun i hi=> ?_) (convex_closedBall ..) (mem_closedBall_self zero_le_one) (show u∈ _ from (by simpa using hu)); rotate_left
   · rw [← norm_iteratedFDeriv_one]; exact (H i hi).norm_le _ le_rfl
   apply le_of_mul_le_mul_right _ hp; unfold Gauge.chord; change _ / G.colorScale * _≤_; rw[div_mul_cancel₀ _ hp.ne']; refine (le_trans ?_ (b:= T*‖u‖) ?_)
   · simpa [f] using ht
   apply le_trans (le_of_eq (b:=(T/G.colorScale*‖u‖)*G.colorScale) ?_); exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_right ..) (norm_nonneg u)) hp.le; field_simp
lemma sailK(G:Gauge) (m:ℕ) : ∃ Z:ℝ,0< Z∧∀ᶠ x:ℝ in atTop, 64*(Z*peace x) ≤ thetaP x∧∀ (i:ℕ), i ∈ range m→∀ u:G.Color, ‖u‖ ≤1→G.chord (G.lieExp ((loc i*peace x) • u)) ≤ Z*peace x:=by
   obtain ⟨K,h,H⟩:=layL G; let M:=kettle m; have hm:0 < M:= loc_pos m; let Z:=K*M; have hz:0 < Z:=by positivity
   refine ⟨Z,hz,?_⟩
   have hQ := (Lim.prod (board hm.le) cool).tiny (by norm_num)
   filter_upwards[eventually_gt_atTop (0:ℝ), (tendsto_rpow_atTop (show 0 < (1/24:ℝ) by norm_num)).eventually_ge_atTop (64*Z),hQ] with x hx hp he
   have hθ:0<thetaP x:=mul_pos (by positivity : 0< (Real.sqrt x)⁻¹) (Zn.wake ..)
   have hS:0<peace x:=by unfold peace; positivity
   refine ⟨?_,fun i hi u hu=>?_⟩
   · unfold peace; rw[← mul_assoc,← mul_div_assoc]; apply (div_le_iff₀ (by positivity)).mpr; linarith only [mul_le_mul_of_nonneg_left hp hθ.le]
   have hv:=roof m i (mem_range.mp hi); have ht: ‖(loc i*peace x) • u‖ ≤ M*peace x :=by rw [norm_smul, Real.norm_of_nonneg (by positivity[hv.1])]; exact (mul_le_of_le_one_right (by positivity[hv.1]) hu).trans (mul_le_mul_of_nonneg_right hv.2 hS.le)
   exact (H _ (ht.trans he)).trans ((mul_le_mul_of_nonneg_left ht (by positivity)).trans_eq (mul_assoc ..).symm)
lemma shifts (x:ℝ)(S:Stage)(Λ:ℝ)(R:Rep G n)(h:Age S x Λ R): sash S x=Cube.moduleBill R.p (high x):=by unfold sash Cube.moduleBill;rw[h.thresh,h.paid];
private lemma vCast {a b:ℕ}{T:Collar G a}(h:a=b) : (h ▸ T : Collar G b).r=T.r:=by subst b;rfl
lemma cast_shape(G:Gauge)(S:Stage)(m d:ℕ)(T:Collar G S.order):∃ Z:ℝ,0 < Z∧∀ᶠ x:ℝ in atTop,∀ (h:ℕ), 1100≤h→ h ≤ towerH x d→∀ (Λ:ℝ)(n:Side)(R:Rep G n)(hs:Age S x Λ R),
    let B:=R.p; let T':Collar G B.order:= hs.rank.symm ▸ T
    let r:= Cleft x h; let u:=Z*peace x
    ToolF m h r x (peace x) R∧ 64*u≤ B.threshold ∧ (∀ i∈range m,∀ v:G.Color,‖v‖≤1 → G.chord (G.lieExp ((loc i*peace x) • v)) ≤ u) ∧ Cube.Wire B 8 T'∧ Cube.Wire B (high x) T' ∧
    Cube.moduleBill B r ≤ 1 ∧ ∀ o∈ Bay n x,halo 9 {o}⊆ tempQ x:=by
   obtain ⟨Z,hZ,H⟩:= sailK G m
   let F(x):=(1+(Cleft x (towerH x d):ℝ))^S.power; have hm: ConstMass 0 F := ((mass zero_le_one).gather (campC d)).crop _
   have hs:= T.pos; have hh:= G.colorScale_pos; have ht:= (Lim.prod tall (ferry hm)).tiny (by norm_num)
   refine ⟨Z,hZ,?_⟩; filter_upwards [H,ht,Work.E01.radiusB_tendsto.eventually_ge_atTop 2,eventually_gt_atTop (1:ℝ), sash_ok S (T.r/G.colorScale/8) (by positivity)] with x H ht hR hx hk h hN he Λ n R hH
   intro B T' r u; rw [← hH.thresh] at H; have hB:= hH.hM.2.1; have hp: 2 ≤ B.B:= hB.symm ▸ hR
   have hr: high x+1≤ r:=by unfold r Cleft; omega
   have hW : Cube.moduleBill B r ≤ 1:=by
       unfold Cube.moduleBill; rw [hH.thresh,hH.paid]; refine le_trans ?_ ht; have ht:= hH.thresh ▸ R.p.threshold_pos; unfold F; gcongr; exact Cleft_mon _ he
   have hy : 8≤high x∧ puff x+9 ≤ high x:=by unfold high; omega
   have hB(r':ℕ)(he:r'≤high x):Cube.Wire B r' T':=by
       have he':T'.r=T.r:=by apply vCast
       have hv' := shifts (G:=G) x S Λ R hH
       have hu : Cube.moduleBill B r' ≤ sash S x:=by rw [hv']; unfold Cube.moduleBill B; gcongr; exact R.p.threshold_pos.le
       refine ⟨?_,le_trans hu (le_trans ?_ hW)⟩
       · rw[he']; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hu.trans hk) (by norm_num)) hh.le); field_simp; linarith
       rw[hv']; unfold Cube.moduleBill B; gcongr; exacts [R.p.threshold_pos.le,by omega]
   refine ⟨⟨?_,hH.high,hp,hH.dialect,fun i hi=> ⟨u,H.1,H.2 _ (mem_product.mp hi).2⟩,fun i hi=> ?_, sprout_mono _ hr⟩,H.1,H.2,hB 8 hy.1,hB _ le_rfl,hW,fun o ho=>?_⟩
   · unfold StemCut; rw[hH.hM.2.1]; unfold rim; nlinarith only [Nat.mul_le_mul_left (radiusB x) hN]
   · let o:=beaconR i.1; have ho:o.1∈Bay n x:= (mem_product.mp ((mem_product.mp hi).1)).1; intro p hP hm w hw; have hp:separation o.1 w ≤ h*(4*B.B+2)+2*B.B:= (Corona.extent _ B.B hP hw).trans (by gcongr); unfold B at hp; rw [hH.hM.2.1] at hp
     obtain ⟨v,hv,h⟩:=halo_spec.mp ((dec_b ..).1 ho); rw [mem_singleton.mp hv] at h; unfold r Cleft; exact halo_spec.mpr ⟨0,mem_singleton_self _, (separation_triangle 0 o.1 _).trans (by omega) ⟩
   obtain ⟨y,hy',hv⟩:= halo_spec.mp ho
   rw [mem_singleton.mp hy'] at hv; exact (hedge hv 9).trans (sprout_mono _ (by omega))
end YM.Trace.Weir
