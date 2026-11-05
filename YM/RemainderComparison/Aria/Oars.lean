import YM.RemainderComparison.Aria.Paint
/-!
 # Cross lighting truth. Energy crew EARLY countable seeds built-in.
 Parameters ask only registration data (no analytic relation of integrated outputs).
 -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Aria
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
    {R:RG.Rep G f} {R':RG.Rep G F}
local notation "B" => radiusB p
variable (hC he)
variable {Z:Site C}{n:ℕ} {a W K₀ v : ℝ} {J : ConnectedActivityE6.Target G K} {o : ConnectedActivityE6.Target.Order G W}
    (C' : Cash W p a L₀ J o K₀ T' R') (c' : Cash W p a L₀ J o v T R) (hq : T'= re T)
    (ht : R'.path=R.path) (hx : R'.p=R.p) (hb:R'.beta=R.beta) (V:Molecule (stepped Q H))(U:Molecule (stepped Q h))
open Gas Ursell Trees Blaze March Lyric WickReps Creek Mosaic Merge Palette Typeface Harmonics Seedlings BoxOf
variable {ι δ:Type}{α:Type*}(X:ι→Portrait R' α) (Y₁:δ→Portrait R α)(u:α)
local notation "X₁"=>brand X u
local notation "Z₁" => brand Y₁ u
variable {I:Type}
variable (k r:ℕ) (X': Score C' I k) (Y': Score c' I k) (z:Site C)
set_option quotPrecheck false
local notation "ψ" => Score.pose C' k X'
local notation "η" => Score.pose c' k Y'
local notation "lT"=> Score.wake C' k n X'
local notation "Lt"=> Score.wake c' k n Y'
local notation "q"=> (Lace.project (h:=h) (H:=H) hC he)
local notation "Lq"=> (Lace.project (h:=h) (H:=H) hC he).low.cut
local notation "aZ" => (X'.index)
local notation "A"=> (Y'.index)
local notation "U₀" => (Score.wake C' k n X').filter fun i=> C'.supportP i⊆neighbors r z
local notation "V₀" => (Score.wake c' k n Y').filter fun i=> c'.supportP i⊆neighbors r (Lq z)
local notation "U₁" => (BoxOf.nearby C' (Timbre.trumpets C') z r n)
local notation "V₁" => (BoxOf.nearby c' (Timbre.trumpets c') (Lq z) r n)
variable (hv: Wears hC he C' c' k X' Y')
variable (hc:2*(r+k+3)<c.val)(hm:2*(r+Mint.width J.halo (radiusB p) (radiusB p))<c.val)
local notation "Sα"=> BoxOf.nearby C' (ψ) z r n
local notation "Sβ"=> BoxOf.nearby c' (η) (Lq z) r n
local notation "p₀"=> reprieve hC he C' c' k X' Y'

lemma antenna {α β:Type*} {F:α→ β}{S₂ T:Set α} (hp:Set.InjOn F S₂)(he:Set.InjOn F T)(hh:∀ i∈ S₂,∀ j∈ T,F i≠F j): Set.InjOn F (S₂∪T):=by
    intro i hi j hj h; rcases hi with hi|hi<;>rcases hj with hj|hj; exact hp hi hj h; exact (hh _ hi _ hj h).elim; exact (hh _ hj _ hi h.symm).elim; exact he hi hj h
include ht hm hv hc
lemma waits : Set.InjOn (p₀) (↑(Sα)) ∧ (Sα).image (p₀)= (Sβ):=by
    let K:= Timbre.bag (h:=h) (H:=H) (Q:=Q) hC he
    have hs i (hp:i∈U₁): p₀ i=K i:=by obtain ⟨j,rfl⟩:= Timbre.knock _ _ _ (mem_filter.mp hp).1; exact (rocks ..).trans (Timbre.pile ..|>.symm)
    obtain ⟨hp,hP⟩:= learns hC he C' c' (n:=n) k r X' Y' z hv hc
    obtain ⟨hκ,hV⟩:= Timbre.snack hC he C' c' ht z r n hm; rw [← Finset.image_congr hs] at hV -- lhs function K view
    rw [show (Sα)=U₁∪ U₀ from Finset.filter_union ..,show (Sβ)=V₁∪ V₀ from Finset.filter_union ..,coe_union,Finset.image_union]; refine ⟨antenna ?_ hp ?_,by rw [hP,hV]⟩
    · intro i hi j hj h; rw [hs i hi,hs j hj] at h; exact hκ hi hj h
    intro i hi j hj; obtain ⟨p,rfl⟩:= Timbre.knock _ _ _ (mem_filter.mp (show i∈U₁ from hi)).1
    obtain ⟨⟨p',v⟩,hv,rfl⟩:= mem_map.mp (mem_filter.mp (show j∈U₀ from hj)).1
    rw [rocks,reads]; intro he; exact Aria.logKey S _ _ he.symm
variable (b:Finset ι)(b':Finset δ)
-- chosen blank E-address injection can require all leaves of a given input arrangement distinct. model.OSt.
variable (θ:↥b≃↥b') (n)
structure Scheduled : Prop where
    turns (i:↥b) : (∃ j,(X i).wing=Wing.logKey j∧∀ s n, j≠X'.index (s,n))∧ (∃ j,(Y₁ ((θ i).val)).wing=Wing.logKey j∧∀ s n, j≠Y'.index (s,n))
    passes (i:↥b) : ((Y₁ ((θ i).val)).wing).support R=((X (i:ι)).wing.support R').image ((Lace.project (h:=h) (H:=H) hC he).high.cut)
    semantics (i : ↥b) (Y' : α) (U:Config G f) : (Typeface.brand Y₁ Y' ((θ i).val)).ingredient U=(Typeface.brand X Y' i.val).ingredient ((Lace.project (h:=h) (H:=H) hC he).high.links U)
    chosen i (hi:i∈b) : C'.supportP ((X i).wing.badge (stepped Q H))⊆ neighbors r z
    injects : Set.InjOn (fun i=>(X i).wing) b
    issued : Set.InjOn (fun i=>(Y₁ i).wing) b'
local notation "qT"=> BoxOf.nearby c' (η) (Lq z) r n
variable (hS:Scheduled hC he C' c' X Y₁ k r X' Y' z b b' θ) -- edit n arg maybe linter unused
include hS
lemma in_deck : ∃ E: Warp («S»:=stepped Q H) (S':=stepped Q h) b b', Folding hC he C' c' X Y₁ u ψ η b b' z r n E:=by
    let ℓ t:= Palette.sign (brand X u) Y t; let σ : ↥b→ Head Y:=fun i=>ℓ i.val; let f'(i:↥b) := Palette.sign (brand Y₁ u) S (θ i).val
    let v:= Function.extend σ f' p₀; let E : Warp b b' (S':=S) («S»:=stepped Q H):= ⟨v,θ,Lq⟩
    have hI : Injective σ:=fun i j h=> Subtype.ext (hS.injects i.prop j.prop (Team.badged _ h))
    have hf(i:↥b): v (ℓ i.val)=f' i:= hI.extend_apply ..
    obtain ⟨hψ,hT⟩:= Aria.waits hC he C' c' ht k r X' Y' z hv hc hm (n:=n)
    have hz(j) (hj:j∈Sα): v j=(p₀) j:=by
       refine Function.extend_apply' _ _ _ ?_; intro hp; obtain ⟨i,h⟩:=hp
       obtain ⟨p,h1,h2⟩:= (hS.turns i).1
       have he:σ i=Opacity.key Y p:=by unfold σ ℓ sign; change (X _).wing.badge _=_; rw [h1]; rfl
       subst j; rcases Finset.mem_union.mp (show σ i∈U₁ ∪ U₀ from (show Sα=U₁ ∪ U₀ from Finset.filter_union ..) ▸ hj) with hi|hi -- cast issue
       · obtain ⟨k,h⟩:= Timbre.knock _ _ _ (mem_filter.mp hi).1; exact Aria.logKey _ _ _ (he.symm.trans h)
       obtain ⟨⟨s,j⟩,-,hq⟩:= mem_map.mp (mem_filter.mp hi).1; exact h2 s j (Wing.logKey.inj (Team.badged Y (he.symm.trans hq.symm)))
    refine ⟨E,⟨?_,(image_congr hz).trans hT,rfl,fun i=> ⟨(hf i).symm, by obtain ⟨⟨j,h,_⟩,⟨j',h',_⟩⟩:=hS.turns i; exact ⟨j,h,j',h'⟩⟩, fun i a=>⟨hS.passes i,hS.semantics i a⟩,fun i=> hS.chosen _ i.prop,?_⟩⟩
    · unfold hub; rw [Finset.coe_union]; change Set.InjOn v _
      apply antenna (F:=v) (T:= (↑(b.image ℓ):Set (Head Y))) (fun i hi j hj h=> hψ hi hj (((hz i hi).symm.trans h).trans (hz j hj)))
      · intro i hx j hy h; obtain ⟨i,hi,rfl⟩:=mem_image.mp hx; obtain ⟨j,hj,rfl⟩:=mem_image.mp hy; let x : ↥b:=⟨i,hi⟩; let y:↥b:=⟨j,hj⟩; rw [hf x,hf y] at h -- motive
        have hv:= θ.injective (Subtype.ext (hS.issued (θ x).prop (θ y).prop (Team.badged _ h)))
        exact congr_arg σ hv
      intro i hi j hy; obtain ⟨j,hj,rfl⟩:=mem_image.mp (Finset.mem_coe.mp hy); let t' : ↥b:= ⟨j,hj⟩; have hq := (hT ▸ mem_image_of_mem p₀ (show i∈Sα from hi)) -- may fail
      obtain ⟨p',hK,hV⟩:= (hS.turns t').2
      have hV' : v (ℓ j)=Opacity.key S p':= by rw [show v (ℓ j)=_ from hf t']; unfold f' sign; change (Y₁ _).wing.badge _=_; rw [hK]; rfl
      rw [hz i hi,hV']; intro he; rw [he] at hq
      rcases mem_union.mp (show _∈ V₁∪ V₀ from (show Sβ=V₁∪ V₀ from Finset.filter_union ..) ▸ hq) with hx|hx
      · obtain ⟨j,hx⟩:= Timbre.knock c' n _ (mem_filter.mp hx).1; exact Aria.logKey S _ _ hx
      obtain ⟨⟨s,j⟩,hh,h⟩:=mem_map.mp (mem_filter.mp hx).1; exact hV s j (Wing.logKey.inj (Team.badged S h.symm))
    intro i hi; have hp: E.f i=p₀ i:=hz i hi; rw [hp]; rcases Finset.mem_union.mp (show i∈ U₁∪ U₀ from (show Sα=U₁ ∪ U₀ from Finset.filter_union ..) ▸ hi) with hi|hi
    · obtain ⟨j,rfl⟩:= Timbre.knock _ _ _ (mem_filter.mp hi).1; exact Or.inl ⟨j,rfl,Aria.rocks ..,((Timbre.chants C' n j).1 (mem_filter.mp hi).1).2⟩
    obtain ⟨⟨s,j⟩,hj,rfl⟩:=mem_map.mp (mem_filter.mp hi).1
    let p:= X'.index (s,j); let q':= Y'.index ((Lq) s,j)
    exact Or.inr ⟨p,q',rfl, Aria.reads ..,hv.inherits s j n (mem_product.mp hj).2,hv.paid s j n (mem_product.mp hj).2⟩
end YM.RemainderComparison.Aria
