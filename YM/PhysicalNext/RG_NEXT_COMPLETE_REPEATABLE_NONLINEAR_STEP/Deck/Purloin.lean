import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Optic
/-! # Illuminate Lap count on any finite Mint wrap. Exact marginal. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Mint
open Poll Pond MeasureTheory ProbabilityTheory
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
section orbit
variable {I J:Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J] (g : I ↪ J) (P : Matrix J J ℝ)
abbrev mount (g:I↪J) (z:Poll.Body J):Poll.Body I:=WithLp.toLp 2 fun i=> z (g i)
def launch (z:Poll.Body I):Poll.Body J:=WithLp.toLp 2 (fun i=> extend g (fun i=> z i) 0 i)
omit [DecidableEq I] [DecidableEq J] in
lemma coast (p:Poll.Body I) (v:J→ℝ) : dotProduct (WithLp.ofLp (launch g p)) v=dotProduct (WithLp.ofLp p) (v ∘ g):= by
  unfold dotProduct; let W:=launch g p; have ht : (∑ i, W i*v i)= ∑ i∈Finset.univ.map g,W i*v i:= Eq.symm (Finset.sum_subset (subset_univ _) (fun i _ hi=> by
    have he : i ∉ Set.range g:= by simpa using hi
    rw [show W i=0 from Function.extend_apply' _ _ _ he, zero_mul]))
  rw [ht,sum_map]; change (∑ i, W (g i)* v (g i)) = ∑ i,p i*v (g i); simp_rw [show ∀ i,W (g i)=p i from fun i=> g.injective.extend_apply ..]
lemma loss (hp:P.PosSemidef): MeasurePreserving (mount g) (Poll.sweep P) (Poll.sweep (P.submatrix g g)):= by
  have hx:Measurable (mount g):=by unfold mount; fun_prop
  refine ⟨hx,Measure.ext_of_charFun (funext fun k=>?_)⟩; have he p : inner ℝ (mount g p) k=inner ℝ p (launch g k):= by
    simp_rw [PiLp.inner_apply,RCLike.inner_apply,starRingEnd_apply,star_trivial]; exact (coast g k p.ofLp).symm
  rw [charFun_apply,integral_map hx.aemeasurable (by fun_prop)]; simp_rw [he, ← charFun_apply]; unfold sweep; rw [charFun_multivariateGaussian hp,charFun_multivariateGaussian (hp.submatrix (↑g)),coast]
  let u:= launch g k; suffices h : (P*ᵥ u.ofLp) ∘ g = P.submatrix g g *ᵥ k.ofLp by rw [show _ = _ from h]; simp
  ext i; change dotProduct _ u.ofLp=dotProduct _ k.ofLp; rw [dotProduct_comm,coast,dotProduct_comm]; rfl
end orbit
include A
lemma draws (y:E.Slice G) (z:E'.Slice G) : Stellar hC he K p (X.wrapY y) (X'.wrapY z) := ⟨A.snow,A.dawn,A.equal,A.reached,A.clips,A.wit,A.views,A.tree,A.reach,A.old,A.wall,A.tall,A.news⟩
variable {U : Finset (Music C F)} {m : ℕ}
def wrappers (L': Lace h H M) (s:Finset (Music C F)) : Finset (Music c f):= s.image (verse_down L')
-- allow p outputs even if Cash.steve costly. budget at anchor in large. Does not require Any mask in proof except hM actually for Θ^.variance
section bear
variable {a v W K₀ : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W} {L₀ : Side}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (hf : X'.manifest) (hm:X.manifest) (hK:X.width=o.K)
    (k k':Finset ℕ)
    (Z:Site C) (n:ℕ) (hZ:2*(2*n)<c.val)
    (hd:Set.InjOn (verse_down (Lace.project (h:=h) (H:=H) hC he)) U)
    (hS:C'.unionP (U.map (disc (stepped Q H)))⊆neighbors n Z) (hw:∀ i∈U,verse R'.path i ≤ radiusB p)
include C' c' A ht hx hb hf hm hK hZ hd hS hw
lemma blankets : let q:= U.map (disc (Y)); let u:=(wrappers (L) U).map (disc (S))
    X'.attains R' J.table W o.a k J.halo q=X.attains R J.table W o.a k' J.halo u := by
  intro q u
  let I:= podium (Y) G (C'.unionP q) X'.B; let g:= X'.body R' J.table W o.a k J.halo q; let f:= X.body R J.table W o.a k' J.halo u
  let l:=L; let x' := radiusB p
  have hz : X'.width=o.K:= A.wit.symm.trans hK
  have hi i (hi:i∈I):separation Z (along (Y) i) ≤ n:= (neighbors_mem ..).1 (hS <| (mem_filter.mp hi).2 (along (Y) i) (by rw [separation_self]; omega))
  have hj:= tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he
  let y:= seed (G:=G) l; let e:↥I ↪ Tubular _ G:= ⟨fun i=> y i.val, fun i k h=> Subtype.ext (hj.point (k:=n) (by omega) Z _ _ (hi _ i.2) (hi _ k.2) h)⟩
  have hE : circuit I X'.relating=X.relating.submatrix e e:= by ext i j; apply A.allocates hZ; refine (separation_triangle _ Z _).trans ?_; rw [separation_comm _ Z]; have hz:=hi _ i.2; have hk:=hi _ j.2; dsimp only; omega
  let a:= arch I X'.relating; have hI:MeasurePreserving (swim I) X'.dice a:= orbit (C'.laws.data.localP E' X' A.reached hz hf).sails.fullC.posSemidef I; have hl:MeasurePreserving (mount e) X.dice a:= by unfold a arch; rw [hE]; exact loss e _ (c'.laws.data.localP E X A.equal hK hm).sails.fullC.posSemidef
  have hx (Y₁:E.Slice G) (Y₂:E'.Slice G): (∫ z,g (Y₂,z) ∂X'.dice) = ∫ z,f (Y₁,z) ∂X.dice:= by
    let a z:=g (Y₂,spill I z); let b z:=g (Y₂,z)
    have ha : Measurable b:= ((X'.body_b J.table_exists (A.reached.symm ▸ C'.laws.intake) (by rw [A.reached,hz]; exact C'.laws.data.access) ..)).comp (measurable_const.prodMk measurable_id)
    have hp : Measurable a:= ha.comp (spill_m I)
    have he (u v) (h : swim I u=swim I v): b u=b v:= C'.concord q (X'.wrapY Y₂) (X'.wrapY Y₂) ⟨Village.refl _ _,(observe _).1 h,fun _ _=> Iff.rfl⟩ A.reached (Finset.Subset.refl _)
    have hy z:f (Y₁,z)=a (mount e z):= by
      rw [show a (mount e z)=b (blow l z) from he _ _ (Pond.settled _ _)]; change _=(X'.wrapY Y₂).term _ _ _ _ _ _ _ _
      unfold f Coat.body; dsimp only; unfold q u Coat.term; rw [prod_map,prod_map]; unfold wrappers; rw [prod_image hd]
      exact Finset.prod_congr rfl (fun i hi=> ((A.draws Y₁ Y₂).granted ht hx hb o.a z J.table i (hw i hi) W J.halo ..).symm)
    rw [Pond.gathered (spill I) (spill_m I) hI (Pond.settled I) he ha]; change (∫ z,a z ∂_) =_
    rw [← hl.map_eq,MeasureTheory.integral_map (by exact hl.measurable.aemeasurable) hp.aestronglyMeasurable]; exact integral_congr_ae (Eventually.of_forall fun i=> (hy i).symm)
  unfold attains; rw [integral_prod _ (C'.integrated X' A.reached hz hf k q),integral_prod _ (c'.integrated X A.equal hK hm k' u)]
  let D := (∫ y,g (X'.Y,y) ∂X'.dice)
  have ht (z:E'.Slice G): (∫ y,g (z,y) ∂X'.dice)= D:= (hx X.Y z).trans (hx X.Y X'.Y).symm
  have hk (z:E.Slice G): (∫ y,f (z,y) ∂X.dice)=D:= (hx z _).symm
  change (∫ z:E'.Slice G, (∫ y,g (z,y) ∂X'.dice) ∂E'.order G)=(∫ z:E.Slice G, (∫ y,f (z,y) ∂X.dice) ∂E.order G)
  simp_rw [ht,hk]; simp

end bear
end YM.PhysicalNext.Repeat.Deck.Stellar
