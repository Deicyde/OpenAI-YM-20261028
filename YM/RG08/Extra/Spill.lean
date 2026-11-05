import YM.RG08.Extra.Extra
/-! # Surface packs after calibration at THE SAME analytic base
-* Missing low orders exactly. Include explicit foil terms line cost. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Spills
open Filter MeasureTheory YM.PertExtension.Series.Tested
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent Finset Next.Free Matrix FreeResolvent Reflect Bloch UVExt.Paths Conductor Virtue Staffer Canon
open PertExtension.Series.Radial PertExtension.Chart PertExtension.GaussianScore
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{F:Panel G}{P Q : Atlas G}{p:Clip}{σ C A B Λ D τ w : ℝ}

lemma foil_plus (j:ℕ)(h:Foil G P j σ A)(he:Foil G Q j σ B)(hp:∀m,AnalyticAt ℝ (P m) 0)(hq:∀m,AnalyticAt ℝ (Q m) 0) : Foil G (P+Q) j σ (A+B) := by
  obtain ⟨X,hX,h⟩:= h; obtain ⟨K,hK,hc⟩:= he; exact ⟨X+K,fun i j=> (hX _ _).add (hK _ _),fun i=> (h i).both (hp i) (hq i) (hc i)⟩
lemma foil_less (j:ℕ)(h:Foil G P j σ A)(he:Foil G Q j σ B)(hp:∀m,AnalyticAt ℝ (P m) 0)(hq:∀m,AnalyticAt ℝ (Q m) 0) : Foil G (P-Q) j σ (A+B) := by
  obtain ⟨X,hX,h⟩:= h; obtain ⟨K,hK,hc⟩:= he; exact ⟨X-K,fun i j=> (hX _ _).sub (hK _ _),fun i=> (h i).less (hp i) (hq i) (hc i)⟩

lemma prefoil (G:Gauge) (j:ℕ)(X:RG.Clip)(A:ℝ)(hp:0<σ) (hA:0≤A) : ∃ w C : ℝ,0<w ∧ 0≤C ∧ ∀ (R:PathData G)(Λ:ℝ), R.Bounds X σ A Λ → Foil G (fun m=> classicFn X R (f:=m)) j w C := by
  obtain ⟨η,M,hη,hM,H⟩:= column_price G j (σ:=σ) A X.direct hp X.quadratic_pos.le
  obtain ⟨u,D,hU,hD,H'⟩:=orbit_cost G 3 j hp; obtain ⟨v,B,hV,hB,hP⟩:=orbit_cost G 4 j hp; let w:=min η (min u v); have hw:0<w:=lt_min hη (lt_min hU hV)
  refine ⟨w,M+A*D+A*B,hw,by positivity,fun R Λ hR=>?_⟩
  obtain ⟨hm,hK⟩:=H X R σ A Λ le_rfl hR hR.rows
  let V m:= inputSeries X R (m:=m); let Y m:= turnSeries R.cubic (m:=m); let Z m:=turnSeries R.quartic (m:=m)
  have ht m : AnalyticAt ℝ (Y m) 0:= turns_analytic R.cubic hp hR.three
  rw [show (fun m=> classicFn X R (f:=m))=V+Y+Z from funext fun m=> intent X R]; refine foil_plus j (foil_plus j (Foil.mono (F:=V) hK hw (min_le_left ..) le_rfl) ?_ hm ht) ?_ (fun m=> (hm _).add (ht _)) (fun m=> turns_analytic R.quartic hp hR.four)
  · exact (show Foil G Y j u (A*D) from H' _ A hR.three).mono hw ((min_le_right ..).trans (min_le_left ..)) le_rfl
  exact (show Foil G Z j v (A*B) from hP _ A hR.four).mono hw ((min_le_right ..).trans (min_le_right ..)) le_rfl

lemma all_pre (G:Gauge) (j:ℕ)(X:RG.Clip)(A:ℝ)(hp:0<σ) (hA:0≤A) : ∃ w C : ℝ,0<w ∧ 0≤C ∧ ∀ (R:PathData G)(Λ:ℝ), R.Bounds X σ A Λ → ∀ k≤j,
    Foil G (fun m=> classicFn X R (f:=m)) k w C ∧ Foil G (fun m=> loopFn R (f:=m)) k w (Λ*C) := by
  choose u D hu hD H using fun j=>prefoil G j X A hp hA
  choose v B hv hB H' using fun j=> orbit_cost G 2 j hp
  induction j with
  | zero=>
     refine ⟨min (u 0) (v 0),D 0+B 0,lt_min (hu _) (hv _),add_nonneg (hD _) (hB _),fun R Λ h k hk=>?_⟩
     rw [show k=0 by omega]; have hx:0≤Λ:= (tsum_nonneg h.two.1).trans h.two.2.2
     exact ⟨(H 0 R Λ h).mono (lt_min (hu _) (hv _)) (min_le_left ..) (le_add_of_nonneg_right (hB _)), (show Foil G _ _ _ _ from H' 0 R.loop Λ h.two).mono (lt_min (hu _) (hv _)) (min_le_right ..) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hD _)) hx)⟩
  | succ n ih=>
     obtain ⟨w,C,hw,hC,h⟩:=ih; let y:=min w (min (u (n+1)) (v (n+1))); have hy:0<y:=lt_min hw (lt_min (hu _) (hv _)); let t := C+D (n+1)+B (n+1); have hz:C≤t:= (le_add_of_nonneg_right (hD _)).trans (le_add_of_nonneg_right (hB _)); refine ⟨y,t,hy,hC.trans hz,fun R Λ hR k hk=>?_⟩
     have hX:0≤Λ:= (tsum_nonneg hR.two.1).trans hR.two.2.2
     by_cases hd:k≤ n; · exact ⟨((h R Λ hR k hd).1.mono hy (min_le_left ..) hz), (h R Λ hR k hd).2.mono hy (min_le_left ..) (mul_le_mul_of_nonneg_left hz hX)⟩
     rw [show k=n+1 by omega]; exact ⟨(H _ _ Λ hR).mono hy ((min_le_right ..).trans (min_le_left ..)) ((le_add_of_nonneg_left hC).trans (le_add_of_nonneg_right (hB _))), (show Foil G _ _ _ _ from H' (n+1) R.loop Λ hR.two).mono hy ((min_le_right ..).trans (min_le_right ..)) (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (add_nonneg hC (hD _))) hX)⟩

-- start unknown packet at rank≥r+2
structure Invoice (P:Atlas G) (F:Panel G)(k n:ℕ) (σ C : ℝ) (T:Flotilla G) : Prop where
    fees : Virtue.exalts T (embark k n) σ C
    pays (m:Side) (j:ℕ) : j≤k+n+1 → Tensor.coeff (P m +shores T (embark k n) m) j 0=recital (F j) m
lemma retrofit (G:Gauge) (r n:ℕ)(h:1≤r)(hp:0<σ): ∃ w C:ℝ,0<w∧ 0≤C ∧ ∀ (P:Atlas G)(A K:ℝ) (F:Panel G), Funds P r n σ K →0≤A→ 0≤K→ (∀ i∈embark r n, Glow (F (i+2)) σ A) →
    (∀ j,Tunable (F j)) → (∀ m,Pointwise (P m) ∧ ∀ i≤r+1,Tensor.coeff (P m) i 0=recital (F i) m)→
    (∀ m:Side,∃ f:Link G m→ℝ,Pointwise f ∧ ∀ i≤ r+n+1,Tensor.coeff f i 0=recital (F i) m)→
       ∃ T:Flotilla G,Invoice P F r n w ((A+K)*C) T := by
  obtain ⟨w,D,hw,he,hD,H⟩:= pilots G n r h hp
  refine ⟨w,D,hw,hD,fun P A K F hP ha hk hF ht hX hz=>?_⟩
  choose V hV Q using hz; let U := V-P
  have hQ m:Pointwise (U m):= (hV m).sub (hX m).1
  have hu : Funds U r n σ (A+K):= by
    intro i hi; refine foil_less (P:=V) _ ⟨gallery (F (i+2)),fun k j=>gallery_funds (hF i hi) hp k j,fun m=> gallery_marks (ht _) (Q _ _ ?_)⟩ (hP i hi) (fun m=> (hV m).analytic) (fun m=> (hX m).1.analytic); simp only [embark,mem_Ico] at *; omega
  have hg (m):Rays (r+2) (U m):= by
    apply (rays_jet (hQ m).analytic _).2
    intro j hj; change iteratedFDeriv ℝ j (V m-P m) 0=0; rw [iteratedFDeriv_sub_apply (hV _).analytic.contDiffAt (hX _).1.analytic.contDiffAt]
    have hy:= (Q m j (by omega)).trans ((hX m).2 j (by omega)|>.symm); rw [sub_eq_zero]; apply smul_right_injective _ (show ((j.factorial:ℝ))⁻¹≠0 by positivity) hy
  obtain ⟨T,hH,hR⟩:= H U _ (add_nonneg ha hk) (fun m=>⟨hQ m,hg m⟩) hu
  refine ⟨T,hH,fun m j hj=>?_⟩
  let Z:= shores T (embark r n) m; have hx:= portside hH hw m
  have hb : Rays (r+n+2) (V m-(P m+Z)):= by rw [show V m-(P m+Z) = U m-Z by change V m-(P m+Z)=V m-P m-Z; abel]; exact hR m
  have hU:= (hX m).1.analytic.add hx.analytic; have hT:= (rays_jet ((hV m).analytic.sub hU) _).1 hb j (by omega)
  rw [← Q _ _ hj]; unfold Tensor.coeff; congr 1
  simp_rw [iteratedFDeriv_sub_apply (hV m).analytic.contDiffAt hU.contDiffAt] at hT
  exact (sub_eq_zero.mp hT).symm
end YM.RG08.Spills
