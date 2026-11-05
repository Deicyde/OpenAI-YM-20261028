import YM.TraceExtension.Perfect.Pulp

set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset Planned.PrimaryIntegral295 Next.Free
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {W:Type*} {n m:W→ Side}(L:Side){η C:ℝ}(F:Filter W){G:Gauge}
variable (g:∀ w,StepData (n w) (m w))(U:∀ w,Link G (n w) → Stationary.Joint G (n w) (m w))(t:∀ w,(g w).Choices)
variable (A:∀ w,CrossA (g w).ratio.count){p:W→Clip}{M:W→ PathData G}
 (hL:∀ w,(g w).ratio.count=L)(hp: ∀ w,Teller (g w) (t w) (p w) (M w) 1 (1:Stationary.Joint G (n w) (m w)))
 (ht:Tendsto (fun w=>(n w).val) F atTop)(he: 0<η)(h :∀ w,(g w).patch.Branches (g w).kernel G)(hC:0≤C)
 (hu:∀ w,Thaw (U w) 0)(hx:∀ w,U w 0=1)(hs:∀ w,(A w).strip η C)(hd:∀ w,Ether (A w))(hX:∀ w,fderiv ℝ (fun x=>content (U w x).1) 0=uniformM (installed (g w).ratio (A w)))
 (x₀:Cover)(v:∀ w,Site (n w))
set_option quotPrecheck false
local notation "x!" => fun w=> ((g w).ratio.embed (v w)+wrap (m w) x₀)
include hL hp ht he h hC hu hx hs hd hX
lemma trough (j:Tit G): Crossed (fun w=>landW (x! w)) F (fun w=> fderiv ℝ (stampA (g w) (t w) (U w)) 0 (ballad j (v w))) (fun w=> inflateA j x₀ (A w) (x! w)) 2:=by
 let f w:= fderiv ℝ (stampA (g w) (t w) (U w)) 0 (ballad j (v w)); let P w:=inflateA j x₀ (A w) (x! w); let y:= x!
 have hh : Modest (fun w=>landW (y w)) F P 2:=by
    obtain ⟨D,d,H⟩:= breeze j x₀ L he hC
    exact ⟨D,d,Eventually.of_forall fun w=> H _ (hL w) (A w) (hs w) _ (y w)⟩
 by_cases hv : j.1=RowGrade.watch
 · have he : ∀ w,f w=P w :=by
      intro w; have hP:P w=((↑↑(g w).ratio.count:ℝ)⁻¹^(ScoreG j)) • ballad j (y w) :=by unfold P inflateA; simp [lowerA,hv]; rfl
      rw [hP]; funext a; unfold f; rw [dot_predict (g w) (M w) (t w) (h w) (hu w) (hx w) (hp w)]
      cases a
      · rw [(ballad_water _ _ hv).2,map_zero]; simp [ballad,hv]
      next i => change (∑ x,_) = _; rw [retired (g w) j (v w) i hv]; simp [ballad,strollT,hv, RowGrade.price,smul_eq_mul]
   exact braid_test ((funext he).symm ▸ hh : Modest (fun w=>landW (y w)) F f 2) (Eventually.of_forall he)
 have hxV(w)(k:Stationary.Lines G (m w) 1) : f w (.inl k)=uniformM (installed (g w).ratio (A w)) (strollT j (v w)) k:=by
     unfold f; rw [dot_predict (g w) (M w) (t w) (h w) (hu w) (hx w) (hp w), hX, (ballad_mix _ _ hv).1]
 have hg(w)(k:Stationary.Lines G (m w) 1) : f w (.inr k)=0:= by
     unfold f; rw [dot_predict (g w) (M w) (t w) (h w) (hu w) (hx w) (hp w)]; simp [ballad, hv]
 have hy(w)(k:Stationary.Lines G (m w) 1):P w (.inr k)=0:=by
     unfold P inflateA; simp only [Pi.add_apply, Finset.sum_apply,Pi.smul_apply, smul_eq_mul, show ballad j (x! w) (Sum.inr k)=0 by simp [ballad,hv],mul_zero,zero_add]
     apply Finset.sum_eq_zero; intro i _; by_cases he:i.1=.watch; rw [medley _ j i x₀ (by rw [ScoreG, ScoreG, he]; exact chapel j.1),zero_mul]; simp [ballad,he]
 obtain ⟨T,hT,H⟩:= sprout L he hC j x₀
 refine ⟨⟨⟨T,hT, Eventually.of_forall fun w i=>?_⟩,hh⟩,?_⟩
 · change |f w i|≤ _; cases i with
   | inl i=> rw [hxV]; exact H _ _ (g w).ratio (hL w) (A w) (hs w) _ i
   | inr i=> rw [hg,abs_zero]; positivity
 intro l ε hε
 have hN:Tendsto (fun w=>(m w).val) F atTop:=tendsto_atTop_mono (show ∀ w,(n w).val≤(m w).val from fun w=>by rw [(g w).sizes]; exact Nat.le_mul_of_pos_right _ (g w).ratio.count.property) ht
 let X(w)(b:Cover)(z:Loc G 1): pairA G (m w) := Sum.inl (wrap (m w) b+y w,z)
 have hk(i:Cover)(z:Loc G 1): Tendsto (fun w=> f w (X w i z)-P w (X w i z)) F (𝓝 0):=by
    have hy:= orbit_gain L (fun w=>(g w).ratio) hL A he hC hs ht j.1 (i+x₀) v j.2.1 z.1
    by_cases hb:z.2=j.2.2
    · refine hy.congr' ?_; filter_upwards [hN.eventually (eventually_gt_atTop (2*size i))] with w hx
      unfold X; rw [hxV,viewTest,if_pos hb, show P w _=_ from amongL (A w) _ _ i j _ _ _ _ hv (rfl : i+x₀=i+x₀) (add_comm _ _) hx (hd _) (hs w) he hC,if_pos hb]; rw [show Carrier.cellar (g w).ratio.count _=_ from congr_arg (fun a:Side=> Carrier.cellar a _) (hL w)]; unfold y; rw [map_add]; abel
    refine tendsto_const_nhds.congr' ?_; filter_upwards [hN.eventually (eventually_gt_atTop (2*size i))] with w hx
    unfold X; rw [hxV,viewTest, if_neg hb, show P w _=_ from amongL (A w) _ _ i j _ _ _ _ hv (rfl : i+x₀=i+x₀) (add_comm _ _) hx (hd w) (hs w) he hC,if_neg hb, sub_zero]
 filter_upwards [(box l|>.eventually_all.mpr fun i _=> eventually_all.mpr (fun z:Loc G 1=> Metric.tendsto_nhds.mp (hk i z) ε hε))] with w hw i hi
 change |f w i-P w i|≤ ε
 cases i with
 | inr i=> rw [hg,hy,sub_zero,abs_zero]; exact hε.le
 | inl i=>
    let b:= lift (i.1 - y w)
    have hX : b∈box l:=by
       change separation (y w) i.1≤l at hi; rw [separation_comm] at hi
       have he(a): (b a).natAbs ≤ l:= (component_le ..).trans hi
       rw [box_test]; constructor<;>intro i<;>specialize he i<;>omega
    have he:= hw b hX i.2; rw [show X w b i.2=Sum.inl i from ?_,dist_zero_right] at he; exact he.le
    unfold X b; rw [wrap_lift]; simp
end YM.Trace.Perfect
