import YM.RemainderComparison.Lobby.Areas

/-! # Queryable Mask leak index. Distinct from gas input P.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lobby
open Function Filter Lattice RG Pressure Tree Wilson MeasureTheory ProbabilityTheory Finset
open Push Push.AbsoluteSums Animals Precision Exterior Next.Fluctuations SectorMeasure Work.E03 Work.F03
open ConnectedActivityE6 Channel Coat Blaze March Poll Brush Blaze.Frond
open PhysicalNext PhysicalNext.Repeat Song Push.Uniform Sienna Fare Lapis Boulevard Metric Lantern Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration
open YM.RemainderComparison.Aux Portal WickReps
open Progress.DirectedRecipe
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge} {ι β I J:Type} {α:Type*} {c f:Side} [DecidableEq β] {Jm:Marker.Census β}
variable (O:Manor G c ι α I) (T:Manor G c ι α J) (P:BudgetPoint)(root:ι→Support c) (K : Set J) (k:ℕ)
variable (a:α)(Z:Set ι)(z:ι→Marker.Poly Jm)
open Mosaic Serif Manor Flues

-- generic letters before Ovens.α (Keep countable)
structure Vesuvius (G:Gauge) (c:Side) (ι α':Type) (α:Type*) where
    site : α'→ Support c
    yeah i : (site i).Nonempty
    log : α→ α'→ Config G c→ℝ
    opus : α'→ Multiset ι
namespace Vesuvius
variable (H: Vesuvius G c ι I α)(S:Vesuvius G c ι J α) {v u γ τ ψ:ℝ}
structure Works (σ b d:ℝ): Prop where
    oasis i a : Tidy P (H.site i) (H.log a i)
    quest i a : Flues.apex root (H.site i) (H.opus i) (H.log a i)
    happy i a V : Healthy P.threshold (H.site i) V → H.log a i V=0
    fortune : ∃ c b':I→ℝ,(∀ i,0≤ c i)∧ (∀ i,0≤ b' i)∧ Ac.Hit H.site P.B c σ b ∧ Ac.Hit H.site P.B b' σ d∧ ∀ i a V, ‖H.log a i V‖ ≤ if Verse.load Z (H.opus i)=0 then c i else b' i

def Assembles (H: Vesuvius G c ι I α) (S:Vesuvius G c ι J α):Vesuvius G c ι (I⊕J) α:= ⟨Sum.elim H.site S.site,fun i=> by rcases i with i|i; exact H.yeah i; exact S.yeah i,fun a=> Sum.elim (H.log a) (S.log a), Sum.elim H.opus S.opus⟩
lemma assembled (h:H.Works P root Z γ u v)(hf:S.Works P root Z γ τ ψ): (Assembles H S).Works P root Z γ (u+τ) (v+ψ):=by
    obtain ⟨c,b,hc,hb,hv,hw,hK⟩:=h.fortune; obtain ⟨c',b',hc',hb',hv',hw',hS⟩:=hf.fortune
    constructor
    · intro i a; rcases i with i|i; exact h.oasis i a; exact hf.oasis i a
    · intro i a; rcases i with i|i; exact h.quest i a; exact hf.quest i a
    · intro i a; rcases i with i|i; exact h.happy i a; exact hf.happy i a
    refine ⟨Sum.elim c c',Sum.elim b b',(fun i=>?_),(fun i=>?_), Labels.together H.site S.site P.B hv hv',Labels.together H.site S.site P.B hw hw',fun i a U=>?_⟩
    · rcases i with i|i; exact hc _; exact hc' _
    · rcases i with i|i; exact hb _; exact hb' _
    rcases i with i|i; exact hK i a U; exact hS i a U

variable (f': I ↪ ℕ)

def spring : Scone ι α G c:= ⟨ Function.extend f' H.site (fun _=>{0}),fun i=>by
 by_cases h:i∈ Set.range f'
 · obtain ⟨i,rfl⟩:=h; rw [f'.injective.extend_apply]; exact H.yeah _
 rw [extend_apply' _ _ _ h]; exact singleton_nonempty _,stuff f' H.opus,fun a=>stuff f' (H.log a)⟩
local notation "L" => H.spring f'
lemma inflate (h:H.Works P root Z γ u v): Scone.Rises L P root ∧ Scone.Treasures L Z k P.B γ u v:=by
    constructor
    · have he i a: Tidy P ((L).leg i) ((L).glow a i)∧ Flues.apex root ((L).leg i) ((L).glyph i) ((L).glow a i)∧ ∀ U, Healthy P.threshold ((L).leg i) U → (L).glow a i U=0:=by
         unfold spring; dsimp only; by_cases hm : i∈Set.range f'
         · obtain ⟨i,rfl⟩:=hm; rw [f'.injective.extend_apply,stuffed,stuffed]; exact ⟨h.oasis i a,h.quest i a,h.happy i a⟩
         rw [blank _ _ hm,blank _ _ hm]; exact ⟨Trio.tidy_const _ _,fun _ _ _ h=> False.elim (h rfl),fun _ _=> rfl⟩
      exact ⟨fun a i=>(he i a).1.uses,fun a i=>(he i a).1.borel,fun a i=>(he i a).1.invariant,fun i a=> (he i a).2.1,fun i a=> (he i a).2.2⟩
    obtain ⟨c,b,hc,hb,hv,hw,hK⟩:=h.fortune
    have hh i : (L).leg (f' i)=H.site i:= by unfold spring; dsimp only; rw [f'.injective.extend_apply]
    refine ⟨stuff f' c,stuff f' b,Rack.positive _ _ hc,Rack.positive _ _ hb,(fun x=>transfer_budget f' (fun i=>by rw [hh,stuffed]) (fun i hi=>by simp_rw [blank _ c hi]; simp) (hv x)),(fun x=>transfer_budget f' (fun i=>by rw [hh, stuffed]) (fun i hi=>by simp_rw [blank _ b hi]; simp) (hw x)),fun i _ a V=>?_⟩
    unfold spring; dsimp only; by_cases hm:i∈Set.range f'
    · obtain ⟨i,rfl⟩:=hm; simp_rw [stuffed]; exact hK i a V
    simp_rw [blank _ (H.log a) hm, blank _ b hm,blank _ c hm]; simp

def books (V: Config G c)(i:I): Marker.Poly Jm:= (Complex.ofReal (H.log a i V)) • Verse.controls Z z (H.opus i)
local notation "Sʼ" => books a Z z H -- check
variable {gV:β→ℝ}
lemma pi_support (h:H.Works P root Z γ u v) (hγ:0≤ γ) (hZ:Chorus Jm gV Z z k) (V:Config G c): Summable (Sʼ V):=by
   let A:= H.site
   obtain ⟨c,b,hc,hb,hv,hw,hK⟩:=h.fortune
   have hf (i):0 ≤ c i+b i:= add_nonneg (hc _) (hb _)
   have he : Ac.Hit A P.B (fun i=> c i+b i) γ (u+v):=RecursiveSecants079.BothSides.hit_plus hv hw
   have hh : Summable (fun i=> c i+b i):=(Product.everyone_ne A P.B hf (fun i _=> H.yeah i) he).2.1.of_nonneg_of_le hf (fun i=> le_mul_of_one_le_right (hf i) (Real.one_le_exp (mul_nonneg hγ (by positivity))))
   exact (Marker.Poly.budgeted hZ.votes hh (show ∀ i, Marker.Poly.price gV (books a Z z H V i) ≤ c i+b i from fun i=>by
      unfold books; rw [Marker.Poly.adapted,Complex.norm_real]
      refine (mul_le_of_le_one_right (norm_nonneg _) (Serif.bought hZ _)).trans ((hK i a V).trans ?_); split; exact le_add_of_nonneg_right (hb _); exact le_add_of_nonneg_left (hc _))).1
lemma plastic (h:H.Works P root Z γ u v) (hγ:0 ≤ γ) (hZ: Chorus Jm gV Z z k) (V:Config G c) : HasSum ((spring H f').plume Z z a V) (∑' i,Sʼ V i) ∧ Summable (Sʼ V):=by
   have hi i : (L).plume Z z a V (f' i)=H.books a Z z V i:=by unfold Scone.plume spring; dsimp only; rw [stuffed,stuffed]; rfl
   have he i (hp:i∉ Set.range f'): (L).plume Z z a V i=0:=by unfold Scone.plume spring; dsimp only; rw [blank _ _ hp]; simp
   have hg:= pi_support P root k a Z z H h hγ hZ V
   refine ⟨(f'.injective.hasSum_iff he).mp ?_, hg⟩
   rw [show ((L).plume Z z a V) ∘ f'= books a Z z H V from funext hi]; exact hg.hasSum
end Vesuvius
end YM.RemainderComparison.Lobby
