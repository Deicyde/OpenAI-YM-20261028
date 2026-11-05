import YM.RemainderComparison.Harmonics.Pass
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Harmonics
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter
open PhysicalNext.Repeat Deck Stellar Mint Poll Pond MeasureTheory ProbabilityTheory Greenbelt Lotus
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Deck.Stellar hC he K p X X') {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p

variable (hC he) (I:Team R) (I':Team R')
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))

structure Youth : Type where
   west : ↥(V\I'.signs (stepped Q H)) ≃ ↥(U\I.signs (stepped Q h))
   verbal (i) : let j:=(west i).val
                (∃ b:Music C F, i.val=Mint.disc (stepped Q H) b ∧ j=Mint.disc (stepped Q h) (Deck.Stellar.verse_down (Lace.project (h:=h) (H:=H) hC he) b)∧verse R'.path b ≤ radiusB p) ∨
                 ∃ j' j₀:ℕ, i.val=Opacity.key (stepped Q H) j' ∧ j = Opacity.key (stepped Q h) j₀ ∧ (R.activities.reg j₀).support=((R'.activities.reg j').support).image (Lace.project (h:=h) (H:=H) hC he).high.cut∧
                  ∀ V:Config G f, Healthy R.p.threshold (R.activities.reg j₀).support V→R'.activities.E j' ((Lace.project (h:=h) (H:=H) hC he).high.links V)=R.activities.E j₀ V
   branch : ↥I'.own≃ ↥I.own
   lungs (i: ↥I'.own) : ∀ V:Config G f, i.val.ingredient ((Lace.project (h:=h) (H:=H) hC he).high.links V)=(branch i).val.ingredient V
   left (i: ↥I'.own) : (branch i).val.crest=i.val.crest.image (Lace.project (h:=h) (H:=H) hC he).high.cut
   lands' (i:↥I'.own) : ∃ j:ℕ, i.val.turn=Wing.logKey j∧∃ j':ℕ,(branch i).val.turn=Wing.logKey j'
   asked : I'.signs (stepped Q H) ⊆ V
   inSquare : I.signs (stepped Q h) ⊆ U
-- laws includes trustworthy Pond.E.C maps. named constructors from Coverage later
variable {hC he I I' U V}
variable (D : Youth (p:=p) hC he I I' V U)
include A ht hx hb D
set_option maxHeartbeats 500000 in
lemma tenants (hZ:2*(n+3)<c.val) (hp:C'.unionP V⊆neighbors n Z) (y:Air f G)(l l':Finset ℕ): I'.premium X' W o.a J.table l' J.halo (Deck.Stellar.blow (L) y) V =I.premium X W o.a J.table l J.halo y U:=by
    unfold Team.premium; rw [if_pos D.asked,if_pos D.inSquare]
    have hv i (hi:i∈V) : areas R' T' J.halo B i⊆neighbors n Z := Finset.Subset.trans (subset_biUnion_of_mem C'.supportP hi) hp
    apply congr_arg₂ (·*·)
    · unfold Team.paidU
      rw [← prod_attach,← prod_attach I.own]
      refine Finset.prod_bij (fun i _=>D.branch i) (fun i _=>mem_attach ..) (fun _ _ _ _ h=> D.branch.injective h) (fun i _=>⟨D.branch.symm i,mem_attach ..,D.branch.apply_symm_apply _⟩) ?_
      intro i _; apply Stellar.buysM A o.a y _ _ (D.left i) hb.symm (D.lungs i) n J.halo Z (hv _ (D.asked (Finset.mem_image_of_mem _ i.2))) hZ
    unfold term
    rw [← prod_attach,← prod_attach (U\I.signs S)]
    refine Finset.prod_bij (fun i _=>D.west i) (fun i _=>mem_attach ..) (fun _ _ _ _ h=> D.west.injective h) (fun i _=>⟨D.west.symm i,mem_attach ..,D.west.apply_symm_apply _⟩) ?_
    intro i _; rcases D.verbal i with ⟨b,h,h',hb'⟩|⟨j,j₁,h,h',hh,hE⟩
    · rw [h,h']; exact A.granted ht hx hb _ _ _ _ hb' .. -- arity
    rw [h,h']; exact Stellar.buysE A _ _ _ _ hh (congr_arg BudgetPoint.threshold hx.symm) hb.symm hE n Z _ _ _ _ _ (h ▸ hv _ (Finset.mem_sdiff.mp i.2).1) hZ
include C' c'
lemma taxation (hZ:2*(2*n+3)<c.val) (hp:C'.unionP V⊆neighbors n Z) (l l':Finset ℕ) (ha:X'.manifest)(hz:X.manifest)(hk:X.width=o.K) :
   I'.tithe X' l' W o.a J.table J.halo V = I.tithe X l W o.a J.table J.halo U:=by
  let V' :=podium Y G (C'.unionP V) X'.B; let g:= I'.into X' W o.a J.table l' J.halo V; let f₀:= I.into X W o.a J.table l J.halo U
  have hx':= A.wit.symm.trans hk
  have hi i (hi:i∈V'):separation Z (along (Y) i) ≤ n:= (neighbors_mem ..).1 (hp <| (mem_filter.mp hi).2 (along (Y) i) (by rw [separation_self]; omega))
  have hj:= Deck.Stellar.tempnest (G:=G) (H:=H) (h:=h) (Q:=Q) hC he
  let y:= Deck.Stellar.seed (G:=G) (L); let e:↥V' ↪ Tubular _ G:= ⟨fun i=> y i.val, fun i k h=> Subtype.ext (hj.point (k:=n) (by omega) Z _ _ (hi _ i.2) (hi _ k.2) h)⟩
  have hE : circuit V' X'.relating=X.relating.submatrix e e:= by
     ext i j; apply A.allocates (D':=2*n) (by omega) -- check
     refine (separation_triangle _ Z _).trans ?_; rw [separation_comm _ Z]; have hz:=hi _ i.2; have hk:=hi _ j.2; dsimp only; omega
  let a':= arch V' X'.relating; have hI:MeasurePreserving (swim V') X'.dice a':= Pond.orbit (C'.laws.data.localP E' X' A.reached hx' ha).sails.fullC.posSemidef V'; have hl:MeasurePreserving (Deck.Stellar.mount e) X.dice a':= by unfold a' arch; rw [hE]; exact Deck.Stellar.loss e _ (c'.laws.data.localP E X A.equal hk hz).sails.fullC.posSemidef
  have hQ := I'.tip X' l' (show Cash W X'.x a L₀ J o K₀ T' R' from A.reached.symm ▸ C') hx' ha V
  have hx (Y₁:E.Slice G) (Y₂:E'.Slice G): (∫ z,g (Y₂,z) ∂X'.dice) = ∫ z,f₀ (Y₁,z) ∂X.dice:= by
    let u z:=g (Y₂,spill V' z); let b z:=g (Y₂,z)
    have hm : Measurable b:= (hQ.1.meas).comp (measurable_const.prodMk measurable_id)
    have hp' : Measurable u:= hm.comp (spill_m V')
    have he (u v) (h : swim V' u=swim V' v): b u=b v:= I'.concur (X'.wrapY Y₂) l' (X'.wrapY Y₂) ⟨Village.refl _ _,(observe _).1 h,fun _ _=> Iff.rfl⟩ (show Room K Y T' X'.x from A.reached.symm ▸ C'.laws.data.room) J.buys (hp:=by show ground R' T' J.halo X'.B V ⊆ C'.unionP V; rw [A.D.1]; exact Finset.Subset.refl _) (A.reached.symm ▸ C'.laws.intake)
    have hy z:f₀ (Y₁,z)=u (Deck.Stellar.mount e z):= by
      rw [show u (Deck.Stellar.mount e z)=b (Deck.Stellar.blow (L) z) from he _ _ (Pond.settled _ _)]
      exact (tenants (A.draws Y₁ Y₂) C' ht (by assumption) hb D (by omega) hp _ _ _).symm
    rw [Pond.gathered (spill V') (spill_m V') hI (Pond.settled V') he hm]; change (∫ z,u z ∂_) =_
    rw [← hl.map_eq,MeasureTheory.integral_map (by exact hl.measurable.aemeasurable) hp'.aestronglyMeasurable]; exact integral_congr_ae (Eventually.of_forall fun i=> (hy i).symm)
  unfold Team.tithe; rw [integral_prod _ hQ.2.1,integral_prod _ (I.tip X l (show Cash W X.x a L₀ J o v T R from A.equal.symm ▸ c') hk hz U|>.2.1)]
  let D₀ := (∫ y,g (X'.Y,y) ∂X'.dice)
  have ht (z:E'.Slice G): (∫ y,g (z,y) ∂X'.dice)= D₀:= (hx X.Y z).trans (hx X.Y X'.Y).symm
  have hk (z:E.Slice G): (∫ y,f₀ (z,y) ∂X.dice)=D₀:= (hx z _).symm
  change (∫ z:E'.Slice G, (∫ y,g (z,y) ∂X'.dice) ∂E'.order G)=(∫ z:E.Slice G, (∫ y,f₀ (z,y) ∂X.dice) ∂E.order G)
  simp_rw [ht,hk]; simp
end YM.RemainderComparison.Harmonics
