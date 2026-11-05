import YM.UVExtension.Forest.Fuses
/-! ℓ¹ strong operator topologies.Home. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Mast
open Filter Function Set MeasureTheory Finset Lattice Wilson RG Labels Extra.Histories
open Push Push.AbsoluteSums Bid Lacing Eyelet Wet Steady RoutesF Source
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι α β : Type}{v: Filter ι}{G:Gauge}
namespace Knot
variable {A Z:Type}[AddCommGroup A][Module ℂ A][NormedAddCommGroup Z][NormedSpace ℂ Z][NeBot v]
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℂ E] [CompleteSpace E]
omit [NormedSpace ℂ Z] in
private lemma walks {f:ι→Z} {x:Z} (hf:Tendsto f v (𝓝 x)): Tune v (fun n (_:Unit)=> f n):=Tune.constant f x hf
variable {b c η:ℝ}
lemma cordial (p:A→ₗ[ℂ] Z)(c:ℂ)(hc:c≠0)(h:DenseRange p)(F:ι→ Z→L[ℂ] E)
    (hb:0< b)(hm:∀ i x, ‖F i x‖ ≤ b*‖x‖) (hx:∀ i:A,∃ z,Tendsto (fun n=> F n (c • p i)) v (𝓝 z))(w:Z): ∃ z,Tendsto (fun n=> F n w) v (𝓝 z):=by
   have hw:DenseRange (c • p):= Dense.mono (by rintro v ⟨i,rfl⟩; exact ⟨c⁻¹ • i,by simp [smul_smul,hc]⟩) h
   refine Wet.leafy ⟨⟨_,Eventually.of_forall fun i _=> hm ..⟩,fun ε he=>?_⟩; obtain ⟨u,hu⟩:= Metric.denseRange_iff.mp hw w (ε/(3*b)) (by positivity); let t:= c • p u; have hv : b*‖t-w‖ ≤ ε/3:= by rw [dist_comm,dist_eq_norm] at hu; refine (mul_le_mul_of_nonneg_left hu.le hb.le).trans_eq (by field_simp)
   obtain ⟨x,hx⟩:=hx u; filter_upwards [(walks hx).uv (ε/3) (by positivity)] with n hn v
   have hf i: ‖F i t-F i w‖≤ ε/3:= by rw [← map_sub]; exact (hm i (t-w)).trans hv
   rw [show F n.1 w-F n.2 w=(F n.1 w-F n.1 t)+(F n.1 t-F n.2 t)+(F n.2 t-F n.2 w) by abel]; apply le_trans (norm_add_le ..); apply le_trans (add_le_add_left (norm_add_le ..) _); rw [norm_sub_rev (F n.1 w)]; exact (add_le_add (add_le_add (hf _) (hn ())) (hf n.2)).trans (by linarith)
lemma flex (F:ι→ Z→L[ℂ] E) {x:ι→ Z}{z:Z}(ht:Tendsto x v (𝓝 z))(hb:0≤ b)(h:∀ i,‖F i (x i-z)‖≤ b*‖x i-z‖){K:E}(hp:Tendsto (fun i=> F i z) v (𝓝 K)): Tendsto (fun i=> F i (x i)) v (𝓝 K):=by
    have he:Tendsto (fun i=>‖F i (x i-z)‖) v (𝓝 0):= squeeze_zero (fun i=> norm_nonneg _) h (show Tendsto .. from (by simpa using! ((ht.sub (f:=x) (g:=fun _=> z) tendsto_const_nhds).norm.const_mul b)))
    have hA:Tendsto (fun i=> F i (x i-z) + F i z) v (𝓝 (0+K)):= ((tendsto_zero_iff_norm_tendsto_zero.mpr he)).add hp
    simp_rw [map_sub,sub_add_cancel,zero_add] at hA; exact hA
end Knot
open Extra.Histories.InputColumn
variable [v.NeBot]{n n': Side}{p P:BudgetPoint}{d:ℕ}{A:Hol G}{F:Frame G d}
variable {L:ι→ RoutesF F n n' p P A}{b u :ℝ}
local notation "J"=> Bucket F P A n
set_option quotPrecheck false
variable (h:∀ i,RoutesF.Counts (L i) u)(hvK:∀ i j,(L i).route=(L j).route)
variable (hP:∀ i z,∃ x,Tendsto (fun n=> (L n).glass i z) v (𝓝 x))(ht:∀ i z,∃ x,Tendsto (fun n=> (L n).wing i z) v (𝓝 x))
include hvK h hP ht
lemma echoes (x:Cow G n' p d A): ∃ K,Tendsto (fun n=> (L n).Pillow x) v (𝓝 K):=by
    obtain ⟨i,-⟩:= (show ∀ᶠ i in v,True from by simp).exists; have he :∀ n m, RoutesF.asset (L n) x m=RoutesF.asset (L i) x m :=by intro n m; unfold RoutesF.asset; rw [hvK n i]
    let F n m:= RoutesF.shell (L n) x m; let f n m (_:Unit):=F n m; let b j:= u*RoutesF.asset (L i) x j
    have hp n j: ‖F n j‖≤b j:= by unfold F; exact ((h n).column x j).trans_eq (congr_arg (u*·) (he n j))
    have hv: Swift v (fun _=>b):= Swift.nil b (u:=_) ⟨fun j=>(norm_nonneg _).trans (hp i j),((L i|>.shelter x).summable.mul_left u),le_refl (∑' j,b j)⟩
    have he(m:Listing):∃ K,Tendsto (fun i=> F i m) v (𝓝 K):=by
       rcases m with _|m|m; · refine ⟨0,(tendsto_const_nhds.congr' ?_)⟩; filter_upwards with i; unfold F RoutesF.shell; simp [RoutesF.roof,consist]
       · obtain ⟨z,hz⟩:= hP (key n' m) (x.1 (key n' m)); exact ⟨_, (ContinuousLinearMap.continuous (rooms n _ _ _ _) |>.tendsto z).comp hz⟩
       by_cases hp : m∈ Set.range (L i).route; swap; · refine ⟨0,tendsto_const_nhds.congr' ?_⟩; filter_upwards with n; unfold F RoutesF.shell RoutesF.roof consist; dsimp only [Sum.elim]; rw [extend_apply' _ _ _ (by rw [hvK n i]; exact hp),Pi.zero_apply,map_zero]
       obtain ⟨j,rfl⟩:=hp
       obtain ⟨z,hz⟩:= ht j (x.2 j)
       let m:Listing:= Sum.inr (Sum.inr ((L i).route j)); refine ⟨_,Tendsto.congr' ?_ (((rooms n (‹Frame G d›) _ P (aisleN (code Listing) m)).continuous.tendsto z).comp hz)⟩; filter_upwards with n; unfold F RoutesF.shell; unfold RoutesF.roof; dsimp only [Function.comp_apply,m,InputColumn.consist,Sum.elim]; rw [show (L n).route=_ from hvK n i,(L i).route.injective.extend_apply]
    have hS:Transit v f:=by refine ⟨⟨_,hv,Eventually.of_forall fun n m v=> hp n m⟩,fun m=>?_⟩; obtain ⟨K,h⟩:=he m; exact Tune.constant _ K h
    exact Wet.leafy (hS.includes (fun (_:Unit) _=> ()))

lemma tempest (hN:∀ a:Option F.Index,∃ x,Tendsto (fun n=>(L n).vane a) v (𝓝 x)) {f:ι→ Cow G n' p d A}{x:Cow G n' p d A}(he:Tendsto f v (𝓝 x))(m:Option F.Index):∃ a,Tendsto (fun i=> (L i).rain (f i) m) v (𝓝 a):=by
    obtain ⟨j,-⟩:= (show ∀ᶠ i in v,True from by simp).exists; obtain ⟨K,hk⟩:= echoes h hvK hP ht x; obtain ⟨c,hc⟩:= hN m
    let T i:=(h i).caravan; have hW:Tendsto (fun i=> T i x) v (𝓝 K):= hk; have hF:= Knot.flex T he (mul_nonneg zero_le_two (h j).calm) (fun i=> (h i|>.serves (f i-x)).2) hW; let P0 : J→L[ℂ] J:= rooms n F A P (aisleN (code Listing) (.inl ()))
    refine ⟨P0 c+ K,?_⟩; simp_rw [fun i=> (h i).rains (f i) m]; exact ((P0.continuous.tendsto c).comp hc).add hF
end YM.UVExtension.Mast
