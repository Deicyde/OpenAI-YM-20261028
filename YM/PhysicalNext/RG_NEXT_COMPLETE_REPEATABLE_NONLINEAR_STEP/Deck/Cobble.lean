import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Roused
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Squirms
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Sylvan
/-! # Value under Stella for Mint pennies. 
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck.Stellar
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Mint
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval
variable {G : Gauge} {c f C F:Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} {hC : C.val=c.val*M} {he:2 ≤ c.val}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T: Tube G (stepped Q h)} {T': Tube G (stepped Q H)} {p : ℝ} {E: Forest (stepped Q h).ratio} {E':Forest (stepped Q H).ratio}
    {X: Coat T E} {X': Coat T' E'} (A : Stellar hC he K p X X')
local notation "B" => radiusB p
abbrev minnow (L': Lace h H M) : Miniature C F→ Miniature c f:= Sum.map (Prod.map id (Deck.spo L')) (Sum.map (curr L'.high.cut) (curr L'.high.cut))
def verse_down (L': Lace h H M) : Music C F→ Music c f:= Sum.map (turn_down L') (Sum.map (turn_down L') (Sum.map (turn_down L') (minnow L')))
abbrev blow (L':Lace h H M) (z:Air f G): Air F G:= WithLp.toLp 2 (z.ofLp ∘ seed L')
include A
lemma rolls (β : ℝ) (z:Air f G): X'.liftA β (blow (L) z)= Deck.light (L).high.cut (X.liftA β z):= by unfold liftA; rw [A.mus]; rfl
lemma hotnext (i:Bond F): X'.Hot i↔X.Hot (curr (L).high.cut i):= by rw [clean_c X A.snow,clean_c X' A.dawn]; exact (A.tree.pines _).not
lemma fleet : X'.t=X.t := by unfold Coat.t; rw [A.equal,A.reached]
lemma sig (i:Bond F) (a:ℝ) (u:Directions G f): X'.cone a (Deck.light (L).high.cut u) i=X.cone a u (curr (L).high.cut i):= by unfold cone; rw [A.fleet,A.clips]; rfl
lemma terrace (Z:Support C) (n : ℕ) (hk:2*(n+3)<c.val) (x:Site C) (he:Z⊆neighbors n x) :
    let p:= (L).low.cut; let g:= curr (L).high.cut (X:=Axis)
    (X.plaza (Z.image p))=(X'.plaza Z).image g ∧ Set.InjOn g (X'.plaza Z) := by
  intro p g
  let l:=L
  let Y' (i:Bond F):= (atEdge (Y) i)
  have hy (i:Bond F) (hi:i∈X'.plaza Z): separation x (Y' i) ≤ n+1:= by
    obtain ⟨z,hz,hv⟩:=not_disjoint_iff.mp (mem_filter.mp hi).2.2; exact (separation_triangle _ z _).trans (add_le_add ((neighbors_mem ..).1 (he hz)) (stride i hv))
  have hh : Nest (Deck.divides hC) g Y' (Shell.atEdge (S)) := (Deck.footing (h:=h) (H:=H) hC (by assumption)).pr
  refine ⟨?_, fun i hi j hj he=> hh.point (k:=n+1) (by omega) x i j (hy i hi) (hy j hj) he⟩; ext i; constructor
  · intro hi; obtain ⟨hx,hy⟩:= (mem_filter.mp hi).2; obtain ⟨y,ht,hQ⟩ := not_disjoint_iff.mp hy; obtain ⟨k,hk',rfl⟩:=mem_image.mp ht
    obtain ⟨j,rfl,hV⟩:=hh.esc k i
    refine mem_image.mpr ⟨j,mem_filter.mpr ⟨mem_univ _,(A.hotnext j).2 hx,not_disjoint_iff.mpr ⟨k,hk',?_⟩⟩,rfl⟩
    have he : separation (Y' j) k≤ 1:= by rw [separation_comm, hV]; exact stride _ hQ
    rw [show ends (S) (g j)=_ from finish_point (hC:=hC) (Q:=Q) j] at hQ
    obtain ⟨x,hb,hc⟩:=mem_image.mp hQ; have ht : x=k:= tiniest (Deck.divides hC) hc ((separation_triangle _ (Y' j) _).trans_lt (by have hD : separation x (Y' j)≤1:=stride j hb; omega))
    exact ht ▸ hb
  intro h; obtain ⟨j,hj,rfl⟩:=mem_image.mp h; obtain ⟨hv,ht⟩ := (mem_filter.mp hj).2; obtain ⟨y,hY,hj'⟩:= Finset.not_disjoint_iff.mp ht
  refine mem_filter.mpr ⟨mem_univ _,(A.hotnext j).1 hv,not_disjoint_iff.mpr ⟨_,mem_image_of_mem p hY,?_⟩⟩; rw [show ends (S) (g j)= _ from finish_point (Q:=Q) (hC:=hC) j]; exact mem_image_of_mem _ hj'
lemma porter (Z:Support C) (n : ℕ) (hk:2*(n+3)<c.val) (x:Site C) (he:Z⊆neighbors n x) (a:ℝ) (u:Directions G f) : X'.enforce a (Deck.light (L).high.cut u) (X'.plaza Z)=X.enforce a u (X.plaza (Z.image (L).low.cut)):= by
  obtain ⟨hV,hG⟩:= A.terrace Z n hk x he; rw [hV]; unfold enforce; rw [prod_image hG]; simp_rw [A.sig]
lemma vexed (s:Signed) (u:Directions G f) (i:Spot C F): X'.extracted (Deck.light (L).high.cut u) s i=X.extracted u s (Deck.spo (L) i):= by
  have hZ j:X'.surcharge s j (Deck.light (L).high.cut u)=X.surcharge s (rod (L) j) u:= by unfold surcharge; rw [if_pos (selected_s X' A.dawn _ _),if_pos (selected_s X A.snow _ _),A.lays]
  rcases i with i|i|i
  · unfold Coat.extracted; change (∑ z∈parents (.inl i),_)= ∑ z∈parents (.inl (curr (L).high.cut i)), _
    simp only [parents,hZ]; simp
  · unfold Coat.extracted; change (∑ j∈parents (.inr (.inl i)),_) = ∑ j∈parents (.inr (.inl (curr (L).low.cut i))),X.surcharge s j u; simp only [parents,sum_singleton,hZ]; rfl
  rfl
lemma flight (i: Spot C F) (s:Signed) (u:Directions G f): X'.light (Deck.light (L).high.cut u) s i=X.light u s (Deck.spo (L) i):= by
  let l:= L; have ht:= A.old; let W:= X.input u
  unfold Coat.light; rw [A.vexed,(A.glassU u).2.2,A.views,A.reach,A.equal,A.reached]; apply congr_arg₂ HSub.hSub _ rfl
  have hz:∀ V: Config G c,pull s 0 (l.low.links V)=l.low.links (pull s 0 V):=fun V=> constellation hC s V
  have hp : pull s 0 (l.high.links W)=l.high.links (pull s 0 W):= constellation (fineP h H hC) s W; rw [hp,hz]
  apply stems hC (by assumption) A.tall A.old A.wall _ A.rank
  rw [← hp]; exact spun hC (by assumption) W X.k s (SectorMeasure.funds_branch ht.accepted)
end YM.PhysicalNext.Repeat.Deck.Stellar
