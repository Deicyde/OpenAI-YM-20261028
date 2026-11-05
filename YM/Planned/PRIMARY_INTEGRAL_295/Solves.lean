import YM.Planned.PRIMARY_INTEGRAL_295.Ritual
import YM.Push.LOCAL_SPLITTING.Padding
/-!
# Pass contracts to smooth real physical unmasked analytic E.LogBank

When campground around V parameter crystal, use true projection and *same*
measure transformed in compactly cut charts. Doesn't assert any uniform
(in levels) smooth extension charges (use Height Charter for earnings). REAL
Regales here on pose.E space, no fake static paths.Pipe.Al. -/
set_option autoImplicit false
noncomputable section
namespace YM.Planned.PrimaryIntegral295.Solves
open Function Filter Set Metric MeasureTheory ProbabilityTheory Matrix Finset
open Lattice RG Wilson Pressure Labels Source Precision Exterior Tree Carrier Bloch Progress.StationaryScenes Bazaars Launch Shapes
open Villa Floor Glints Fizz Fizz.Gush Little Density Little.Core Push.Uniform Sparks Night Barges Novas Novas.Torch Mansions Decks Castles Ritual
open Icebergs Tropics Kelps Nimbuses Streets Dawning Cabins Cedar Next.Fluctuations Ripple Porous
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius RealInnerProductSpace Classical
variable {G:Gauge} {E:Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {k r n d χ:ℕ} {c f:Side} {t ξ C M s : ℝ}
variable {F:Labels.Frame G d} {S:StepData c f} {Q:Teller G}

-- analysis uniform only within each stratum.A Sel. Probe neighborhood.
section Paid
variable {Y:Type} [NormedAddCommGroup Y][NormedSpace ℝ Y]
lemma richest (f:E→Y)(k:ℕ):∃ u:ℝ, Oval.Envelope 0 k f u:=by
   let z(i:ℕ):= ‖iteratedFDeriv ℝ i f 0‖
   exact ⟨_,Finset.sum_nonneg (s:=range (k+1)) (fun i _=>norm_nonneg (iteratedFDeriv ℝ i f 0)),fun i hi=> Finset.single_le_sum (fun i _=>norm_nonneg (iteratedFDeriv ℝ i f 0)) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))⟩
-- compact radius parametric path guard for square.C closures.
omit [NormedSpace ℝ E] in
private lemma cooler {ι:Type}[Fintype ι](F:E→Plate ι)(N:ℝ) (h:ContinuousAt F 0)
   (hr:∃ u:ℝ,0≤u ∧∀ x:Sky ι,‖x‖≤u*‖F 0 x‖) : ∃ D:ℝ,∀ᶠ x in 𝓝 0,∀ y:Sky ι,D<‖y‖→N<‖F x y‖:=by
   obtain ⟨u,hu,ht⟩:=hr
   let C:=1+u; have hC : 1 ≤ C:=le_add_of_nonneg_right hu; set r:=(2*C)⁻¹
   have he := h.eventually (ball_mem_nhds _ (show 0<r by unfold r; positivity))
   refine ⟨N*(2*C),?_⟩; filter_upwards [he] with x hx y hy
   have ha: ‖F 0 y‖ ≤ ‖F x y‖ + r*‖y‖ :=by
      rw [add_comm]; apply (norm_le_norm_sub_add _ (F x y)).trans
      have hs : ‖F 0-F x‖≤r:=by rw [←dist_eq_norm,dist_comm]; exact (mem_ball.mp hx).le
      exact add_le_add_left (((F 0-F x).le_opNorm y).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))) _
   have hv := (ht y).trans (mul_le_mul (show u≤C by unfold C; simp) ha (norm_nonneg _) (zero_le_one.trans hC))
   have hp : 2*C*r=1:= mul_inv_cancel₀ (by positivity)
   have hw' : N*(2*C) < ‖F x y‖*(2*C) := by have h1:= congr_arg (·*‖y‖) hp; nlinarith
   exact lt_of_mul_lt_mul_right hw' (by positivity)
-- derivative pass generic finite compact. vertical derivative identity
variable [FiniteDimensional ℝ E]
lemma summer {ι:Type}[Fintype ι] (R:Sky ι → E→ ℂ)(k:ℕ)
    (hc:∀ᶠ x in 𝓝 (0:E),∀ i:Sky ι, ContDiffAt ℝ k (Function.uncurry R) (i,x))
    (hp:∃ C:ℝ,∀ᶠ x in 𝓝 (0:E),∀ i:Sky ι,C<‖i‖→R i x=0) : Regales R (stdGaussian (Sky ι)) k 0:=by
   obtain ⟨N,H⟩:=hp
   obtain ⟨r,hr,h'⟩:=Metric.nhds_basis_closedBall.eventually_iff.mp (hc.and H)
   let s:= closedBall (0:E) r; let S:=ball (0:E) r; let g:=R
   let v (n : ℕ) := vertical (uncurry g) n
   have he : IsOpen S := isOpen_ball
   have hz (p:Sky ι×E) (hp : p.2∈s) : ContDiffAt ℝ k (uncurry g) p := (h' hp).1 _
   have hY (n : ℕ) (hn:n≤k) (p:Sky ι×E) (hp : p.2∈s) := vert_cont (hz p hp) hn
   have hd (n : ℕ) (hn:n≤k) (y : E) (hy : y∈s) : AEStronglyMeasurable (report g n y) (stdGaussian (Sky ι)) := by
     have he : Continuous (report g n y) := continuous_iff_continuousAt.mpr fun i=> (hY n hn (i,y) hy).comp (f:=fun z:Sky ι=>(z,y))
        (show ContinuousAt (fun z:Sky ι=>(z,y)) i from continuousAt_id.prodMk continuousAt_const)
     exact he.aestronglyMeasurable
   have hy (y:E) (p:Sky ι) (hY:y∈S) (hp:N<‖p‖) (n:ℕ) : report g n y p=0 := by
     have he' : g p =ᶠ[𝓝 y] 0 := by
       filter_upwards [he.mem_nhds hY] with z hz; exact (h' (ball_subset_closedBall hz)).2 p hp
     unfold report; rw [(he'.iteratedFDeriv ℝ _).self_of_nhds]; simp
   refine ⟨S,mem_ball_self hr,he,Eventually.of_forall (fun z y hy=> ?_),fun n hn y hy=>hd _ hn _ (ball_subset_closedBall hy),fun n hn=>?_⟩
   · exact (hz (z,y) (ball_subset_closedBall hy)).comp (f:=fun u:E=>(z,u)) y (contDiffAt_const.prodMk contDiffAt_id)
   letI:= FiniteDimensional.proper ℝ E
   let T := closedBall (0:Sky ι) N ×ˢ s
   have ht : IsCompact T := (isCompact_closedBall ..).prod (isCompact_closedBall ..)
   obtain ⟨C,hC⟩:= ht.bddAbove_image (f:=fun x=> ‖v n x‖) (show ContinuousOn (fun x=>‖v n x‖) T from
     fun x hx=>((hY n hn x hx.2).norm.continuousWithinAt))
   refine ⟨fun _=>max 0 C,integrable_const _,Eventually.of_forall fun z y hY'=>?_⟩
   by_cases hp : ‖z‖≤N
   · exact (show ‖v n (z,y)‖≤C from hC ⟨(z,y),⟨by simpa using hp,ball_subset_closedBall hY'⟩,rfl⟩).trans (le_max_right ..)
   rw [show report _ n y z=_ from hy y z hY' (lt_of_not_ge hp) n,norm_zero]; exact le_max_left ..
end Paid

-- Group-level smooth Hank.Display. Finite not uniform, no circular assumption.
private lemma streak {U:E→ Config G f} {x:E}(T:SectionData F)(v:F.Coeff) (h:∀ i,ContDiffAt ℝ k (fun y=> G.mat (U y i)) x):
   ContDiffAt ℝ k (fun y=>T.places v 0 (U y)) x:=by
   let K:=Source.Index G T.stencil
   let p:E→K→ℂ:= fun x=>entry (expandAt 0 (U x))
   have he (i:K): ContDiffAt ℝ k (fun y=>p y i) x:=by
      obtain ⟨i,a,b,c⟩:=i
      let L:G.Mat→L[ℝ] ℂ:= LinearMap.toContinuousLinearMap { toFun A:=A a b,map_add' _ _:=rfl,map_smul' _ _:= rfl }
      let f':= fun y:E=> G.mat (expandAt 0 (U y) i.val)
      have hh:ContDiffAt ℝ k (fun y=>f' y a b) x:=L.contDiff.contDiffAt.comp x (show ContDiffAt ℝ k f' x from h _)
      cases c
      · exact hh
      exact (show ContDiff ℝ k (starL' ℝ : ℂ ≃L[ℝ] ℂ) from (starL' ℝ).contDiff).contDiffAt.comp x hh
   let q:= T.evalC v
   have hp(q:MvPolynomial K ℂ):ContDiffAt ℝ k (fun y=>MvPolynomial.aeval (p y) q) x:=by
      induction q using MvPolynomial.induction_on with
      | C c => simp_rw [MvPolynomial.aeval_C]; exact contDiffAt_const
      | add p q ih ig=> simp only [map_add]; exact ih.add ig
      | mul_X p i ih=> simp only [map_mul,MvPolynomial.aeval_X]; exact ih.mul (he i)
   exact hp q

section Ensemble
variable (P:Torch G S) {T:SectionData F} (h:Relic P Q T r k χ C t M s) (b:E→Dir G c)(hb:‖b 0‖≤M)(hf:ContDiffAt ℝ k b 0)
include h hb hf

lemma burning (hg:ξ∈Set.Ioc (0:ℝ) 1):let Z:= Decks.pose P b t
    ∃ A: E→Plate P.Index, ∃ v:ℝ, (Z.casted ξ A).Soak ξ k v ∧
      ∀ᶠ y in 𝓝 0, MeasurePreserving (A y) (stdGaussian (Sky P.Index)) (multivariateGaussian 0 (Z.C y)) ∧ (Z.C y).PosSemidef :=by
   intro Z
   obtain ⟨hp,hH⟩:= blossom P h b hb hf; let L:=Post.bark k C; have hh : Clear (Z.C 0) L:= (Ritual.ceremony P h b hb).1
   have hs(k): (Z.C k).IsHermitian:=Windows.coin_symmetric ..
   obtain ⟨D,hD⟩:= richest (MapB P.Index∘ Z.C) k; have hc:=h.price.cost
   let v := (Fintype.card P.Index:ℝ)+ D+ L +C
   have hv : 1 ≤ L:=hh.1; have ht:=hh.2.1.apply; have hl:C ≤ v ∧ D≤v ∧ L≤v:=by have hu:=hD.1; have hp:0≤(Fintype.card P.Index:ℝ):=Nat.cast_nonneg _; unfold v; refine ⟨?_,?_,?_⟩<;> linarith
   have hz := h.deck.ridge
   have hk : Z.Kind k v:=by
     constructor
     · refine ⟨hv.trans hl.2.2,hh.2.1,fun z=>?_⟩; have he:= hh.2.2 z
       exact he.trans (mul_le_mul_of_nonneg_right hl.2.2 (nonneg_of_mul_nonneg_right ((sq_nonneg _).trans he) (by linarith)))
     · exact ⟨hp,Seas.less hD hl.2.1⟩
     · exact Eventually.of_forall hs
     · change (Fintype.card P.Index:ℝ) ≤ _; have he:=hD.1; unfold v; linarith
     · exact h.deck.length.trans hl.1
     · exact ⟨hz.1,hz.2.trans (mul_le_mul_of_nonneg_right hl.1 hz.1.1.le)⟩
     · exact fun x=>Seas.less (h.deck.pulse x) hl.1
   obtain ⟨A,hA,hq⟩:= Gush.geyser Z hk hg le_rfl
   refine ⟨A,_,hA,?_⟩
   filter_upwards [hq] with x hx
   suffices H:∀ (D:Matrix P.Index P.Index ℝ)(A:Plate P.Index), A*star A=MapB P.Index D → D.PosSemidef by exact ⟨hx.1,H (Z.C x) (A x) hx.2⟩
   intro D A he; obtain ⟨R,rfl⟩:= (MapB P.Index).surjective A; change MapB _ R * star (MapB _ R)=MapB _ D at he; rw [← Tropics.starMap,← map_mul] at he
   rw [← ((MapB P.Index).injective he)]; exact Matrix.posSemidef_self_mul_conjTranspose R

variable [FiniteDimensional ℝ E]
lemma salubrious (hg:ξ∈Set.Ioc 0 1) (i:F.Index): (∀ᶠ y in 𝓝 0,((Decks.pose P b t).C y).PosSemidef) ∧
     ContDiffAt ℝ k (baron P b t ξ T i) 0 :=by
   obtain ⟨A,v,hs,hA⟩:= burning P h b hb hf hg
   let Z:= Decks.pose P b t; let α:= (t^(F.grades i).2)⁻¹
   let U(y:E): Sky P.Index → Config G f:= Z.lit t ξ y
   let Λ(y:E)(x:Sky P.Index):= Z.globe ξ x • (α • T.places (Place.copy F i) 0 (U y x))
   let g(x:Sky P.Index)(y:E) := Λ y (A y x)
   refine ⟨hA.mono (fun _ h=>h.2),?_⟩
   have hz:= show (baron P b t ξ T i) =ᶠ[𝓝 0] fun y=> ∫ x, g x y ∂stdGaussian (Sky P.Index) from by
     filter_upwards [hA] with y hy
     let μ : Measure (Sky P.Index):= multivariateGaussian 0 (Z.C y)
     have hc: MeasurePreserving (A y) (stdGaussian (Sky P.Index)) μ:=hy.1
     change (∫ x, Λ y x ∂μ)=_
     rw [←hc.map_eq, integral_map hc.measurable.aemeasurable];
     have hm : Continuous (Λ y):=(P.lamps_fine ξ).smul (((SectionData.continuous_places T (Place.copy F i) (0:Site f)).comp (Z.lit_continuous t ξ y)).const_smul α)
     exact hm.aestronglyMeasurable
   suffices H:Regales g (stdGaussian (Sky P.Index)) k 0 by
      obtain ⟨S,hS,H⟩:=H; exact (H.flare 0 hS).congr_of_eventuallyEq hz
   apply summer
   · have hf':ContDiffAt ℝ k A 0:= hs.crown.1; have hm:ContDiffAt ℝ k Z.mean 0:=(blossom P h b hb hf).2
     filter_upwards [hf'.eventually (by simp), hf.eventually (by simp), hm.eventually (by simp)] with y hu he hq x
     let B:= (Sky P.Index) × E; let a:B:=(x,y); let V:B→ Sky P.Index:=fun y=> A y.2 y.1
     have hF:ContDiffAt ℝ k V a:=(hu.comp (f:=Prod.snd) a contDiffAt_snd).clm_apply contDiffAt_fst
     let W:= fun y:B=> U y.2 (V y)
     have hP:(ContDiff ℝ k (Z.globe ξ)):= hs.profile.1
     refine (hP.contDiffAt.comp a hF).smul ((streak (U:=W) T (Place.copy F i) ?_).const_smul α) -- metavars? 
     intro i; change ContDiffAt ℝ k (fun y=> G.mat (W y i)) a
     let u:= Z.tree; let L:Sky P.Index→L[ℝ] AxisChart G u:= P.mist; let H(y:B):AxisChart G u := t • (Z.mean y.2 + ξ • L (V y))
     let D:=fun y:B=> represent (t • b y.2); have hv (y): W y=lifting u (D y) (H y) := rfl
     by_cases hh:i∈Z.tree.trunks
     · have hH(y): W y i=1:= u.on_tree _ ⟨i,hh⟩
       simp_rw [hH]; exact contDiffAt_const
     let q:u.Free:=⟨i,hh⟩; have hx(y) : W y i=G.lieExp (H y q) * replica S.ratio (D y) i := u.off_tree _ q
     simp_rw [hx,G.mat_mul]; apply ContDiffAt.mul
     · have hz : ContDiffAt ℝ k H a:= ((hq.comp (f:=Prod.snd) a contDiffAt_snd).add ((L.contDiff.contDiffAt.comp a hF).const_smul ξ)).const_smul t
       exact (G.exp_jet.of_le le_top).contDiffAt.comp a (contDiffAt_pi.mp hz q)
     unfold replica; split
     · exact contDiffAt_const
     simp_rw [D, Work.F03.represent_link]
     exact (G.exp_jet.of_le le_top).contDiffAt.comp a (contDiffAt_pi.mp ((he.comp (f:=Prod.snd) a contDiffAt_snd).const_smul t) _)
   obtain ⟨N,hN⟩:= cooler A (v/ξ) (hs.crown.1.continuousAt) hs.invert
   refine ⟨N,hN.mono fun x hx i hi=>?_⟩; unfold g Λ; rw [show Z.globe ξ (A x i)=0 from ?_,zero_smul]
   exact (hs.cover (A x i)).2.2 (((div_lt_iff₀ hg.1).mp (hx i hi)).trans_eq (mul_comm ..))

end Ensemble
end YM.Planned.PrimaryIntegral295.Solves
