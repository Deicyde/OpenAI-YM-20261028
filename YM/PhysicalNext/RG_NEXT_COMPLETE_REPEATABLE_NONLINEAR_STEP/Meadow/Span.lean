import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Meadow.Vista
/-!
 # Music park lift at marked width. Includes inverse addressing, so no multiplicative
 weight guessing when κ duplicated.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Meadow
open Function Filter Lattice RG Pressure Tree Wilson Finset Matrix Relation
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel Pulse Animals
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent Shell Census Raw Footprint Matter Deck Mint Greenbelt
open Poll Pond MeasureTheory ProbabilityTheory Stellar Gas Ursell Trees Blaze March
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G : Gauge} {c f C F L₀ : Side} {P : Patch} {M D' : ℕ} {K : Teller G}
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q: KernelChoices} {hC:C.val=c.val*M} {he:2 ≤ c.val} {p a b W U V : ℝ}
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable {T : Tube G (stepped Q h)} {T' : Tube G (stepped Q H)} {R:RG.Rep G f} {R':RG.Rep G F}
    {X : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    {I : Cash W p a L₀ X o U T R} {I' : Cash W p a L₀ X o V T' R'}
    (hC he)
local notation "B" => radiusB p
local notation "D" => roomSize X.halo B
local notation "t" => Mint.width X.halo B B
variable (x : Site C)
def forward (V:Lace h H M) (p:Vines C F) : Vines c f:= ⟨p.fst, wrappers V ∘ p.snd⟩
include hC
lemma garden (he : 2*D'<c.val) : Set.InjOn (Macrame.splitter (Deck.divides hC)) (neighbors D' x):= by
  intro i hi j hj h; apply tiniest _ h; apply (separation_triangle _ x _).trans_lt; rw [separation_comm i]; have h₁ := (neighbors_mem ..).1 (Finset.mem_coe.mp hi); have h₂:= (neighbors_mem ..).1 (Finset.mem_coe.mp hj); omega
include he
lemma genitive (hh : 2*D'<c.val) {v w: Park C F} (hz:∀ i∈v,separation x (pace (Y) i)≤D') (ht:∀ i∈w,separation x (pace (Y) i)≤D') (hp:wrappers (L) v=wrappers (L) w) : v=w:= by
  let L':=verse_down (L); have he:=Stellar.nest_mint (hC:=hC) (he:=he) (h:=h) (H:=H) (Q:=Q); ext i; constructor
  · intro hi; obtain ⟨j,hj,hp⟩:= mem_image.mp (show L' i∈ wrappers (L) w from hp ▸ (show L' i ∈ wrappers (L) v from mem_image_of_mem L' hi)); exact (he.point hh x i j (hz i hi) (ht j hj) hp.symm).symm ▸ hj
  intro hi; obtain ⟨j,hj,hp⟩:=mem_image.mp (show L' i∈wrappers (L) v from hp.symm ▸ (show L' i∈wrappers (L) w from mem_image_of_mem L' hi)); exact (he.point hh x i j (ht i hi) (hz j hj) hp.symm).symm ▸ hj
omit hC he in
lemma engirds (v:Vines C F) (hv:Stir I' v) (hz:x∈Meadow.pasture I' v) (i): Meadow.ground I' (v.2 i)⊆neighbors D x:= (your (H:=I') (z:=v) i).trans (entered hv x hz)
lemma inquire (v u: Vines C F) (hv:Stir I' v) (hu:Stir I' u) (hx:x∈Meadow.pasture I' v) (hk:x∈Meadow.pasture I' u) (hC':2 * D < c.val) (h:forward (L) u=forward (L) v): u=v:= by
  have he : u.fst=v.fst:= congr_arg (fun i : Vines c f=> i.fst) h; rcases v with ⟨n,v⟩; rcases u with ⟨m,u⟩; dsimp only at he; subst m
  unfold forward at h; injection h with h hh; congr 1; funext i; let V:=v
  apply genitive (Q:=Q) hC (by assumption) x hC' _ _ (congr_fun hh i)
  · intro j hk'; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,u⟩) i|>.trans (entered hu x hk)) (centers (hu.each i) hk'))
  intro j hk; exact (neighbors_mem ..).1 ((your (H:=I') (z:=⟨_,v⟩) i|>.trans (entered hv x hx)) (centers (hv.each i) hk))
lemma rings (v:Vines C F) (hv:Stir I' v) (hx:x∈ Meadow.pasture I' v) (hp:2*D<c.val) (i) : Set.InjOn (verse_down (L)) (↑(v.2 i) : Set (Music C F)):= by
  have hI:= engirds x v hv hx i
  intro y hy z hz he; exact (nest_mint (Q:=Q) (hC:=hC) (he:=by assumption) (h:=h) (H:=H)).point hp x y z ((neighbors_mem ..).1 (hI (centers (hv.each i) hy))) ((neighbors_mem ..).1 ((your (H:=I') (z:=v) i).trans (entered hv x hx) (centers (hv.each i) hz))) he
variable (hp : R'.path=R.path)
include hp I I'
lemma pitchRoll (z: Vines C F) : Meadow.pasture I (forward (L) z)= (Meadow.pasture I' z).image (L).low.cut:= by unfold pasture forward; unfold unionOf; ext i; simp only [Function.comp_apply, mem_image,mem_biUnion,pitched (I:=I) (I':=I') hC he hp]; grind
lemma receipts (z:Vines C F) (hZ:2*D'< c.val) (hz: Meadow.pasture I' z⊆ neighbors D' x) (hu: ∀ i,Seed I' (z.2 i)) :
    coefficient (blocked (Meadow.ground I')) z.2=coefficient (blocked (Meadow.ground I)) (forward (L) z).2:= by
  apply movement; intro i j; let f:=Meadow.ground I'; have hf i: f (z.2 i)⊆neighbors D' x := (your (H:=I') (z:=z) _).trans hz
  have hm i s (hh:s∈z.2 i):separation x (pace Y s) ≤ D':= (neighbors_mem ..).1 (hf i (centers (hu i) hh)); have hv i: ((Meadow.ground I ∘ (forward (L) z).2) i)=(f (z.2 i)).image (L).low.cut:= pitched hC he hp _
  have hy i : Meadow.ground I ((forward (L) z).2 i)= (f (z.2 i)).image (L).low.cut:= hv i
  apply or_congr; · exact ⟨fun hx=>congr_arg (wrappers (L)) hx,genitive hC he x hZ (hm i) (hm j)⟩
  unfold Ac.meets; rw [hy,hy]; constructor
  · rintro ⟨v,h,hx⟩; exact ⟨_,mem_image_of_mem _ h,mem_image_of_mem _ hx⟩
  rintro ⟨v,h',hx⟩; obtain ⟨z,hv,hj⟩:=mem_image.mp h'; obtain ⟨y,hy,hr⟩:=mem_image.mp hx
  -- compare labels via hZ; priority
  exact ⟨z,hv, ((garden hC x hZ) (hf _ hy) (hf _ hv) (hr.trans hj.symm)) ▸ hy⟩
lemma stitches (z:Vines C F) (hv:Stir I' z) (hk:x∈Meadow.pasture I' z) (hH:2 * D< c.val) : Stir I (forward (L) z) ∧ (L).low.cut x∈Meadow.pasture I (forward (L) z):= by
  have hS:= entered hv x hk
  refine ⟨⟨hv.small,fun i=> ?_,((receipts (I':=I') hC he x (I:=I) hp z hH hS hv.each) ▸ hv.moves)⟩,?_⟩
  · apply (seed_order (I:=I) (I':=I') hC he hp _ (rings hC he x z hv hk hH i) ((garden hC x hH).mono _)).1 (hv.each i)
    exact coe_subset.mpr ((your (z:=z) i).trans hS)
  rw [pitchRoll (I:=I) (I':=I') hC he hp z]; exact mem_image_of_mem _ hk
end YM.PhysicalNext.Repeat.Meadow
