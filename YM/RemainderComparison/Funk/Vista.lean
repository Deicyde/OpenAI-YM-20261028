import YM.RemainderComparison.Funk.Prelude
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Funk
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Greenbelt Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling OmitClusters AnalyticBridge.VerifiedReset
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι δ : Type} {α:Type*}
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ w C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
open Aux Mosaic Verse Muse Apo Marker Push.Uniform Lapis Sienna Fare Boulevard Herbal WickReps Lyric Typeface
open Trio Next.Rank.Glyph Next.Rank.Exponential
variable (Q:ConnectedActivityE6.Target G P) (Ω:KernelChoices)
open Lobby Portal
open Pier Slide
variable {β:ℝ}{χ:Chi}{ιa ιb δa δb:Type}(P': BudgetPoint)
variable {A : Manor G c ι α ιa} {Ba : Manor G c ι α ιb} {AA : Set ιa} {p q w z r' k d : ℕ}
section
variable (V : Pier c G W x μ L Q o C β χ α) (T': Pier.Cuts Q χ V) (j:ℕ)
structure Chairs (r:ℕ) where
    raw : Manor.Basis (Pier.vane Q χ V) T'.A r
    model : V.spill.Basis T'.B r
variable {V T'} {hx : Chairs Q V T' r'}

-- Grouped vacuum template derived signs in body.BALL
open Manor
lemma froth_price (A: Manor G c ι α ιa)(t:Finset ιa)(B:A.Basis t r')(u:α) : Trio.froth (A.sector u t B)= Apo.slab A t u:=by
    funext x; unfold Trio.froth Manor.sector Apo.slab; rw [sum_comm]; refine sum_congr rfl fun i hi=>?_ ; rw [← sum_mul,B.account i hi,one_mul]
lemma shade_add {Y:Stars→Side}(f g:Offer G c)(X Y':∀ i:Stars,Offer G (Y i))(he:WickReps.Sensible P' p f X)(ht:WickReps.Sensible P' p g Y'): WickReps.Sensible P' p (f-g) (X-Y'):= by
   refine ⟨fun i a v b U h=> congr_arg₂ (·-·) (he.moves i a v b U h) (ht.moves i a v b U h), fun i j u v A B hA hB hT=> ?_,fun i u v A B hA hB hT=>?_ ,fun x U V hx=> congr_arg₂ (·-·) (he.visitL _ _ _ hx) (ht.visitL _ _ _ hx)⟩
   · exact congr_arg₂ (·-·) (he.pace i j u v A B hA hB hT) (ht.pace i j u v A B hA hB hT)
   exact congr_arg₂ (·-·) (he.forks i u v A B hA hB hT) (ht.forks i u v A B hA hB hT)

-- Lift earnings to neighboring stem mask failure. before SO.Stamp.
local notation "Gr"=> Pier.Cuts
variable {X:Set (AA⊕ιb)} {tS:Finset (AA⊕ιb)} {σ η R' V₀ Yv p₀:ℝ}
local notation "M₀"=> Lobby.mural A Ba AA

-- Body vac basis split before Compatibility
variable (A Ba AA tS)
def chairs₁ (V: (mural A Ba AA).Basis tS r') : Basis (Lobby.peel A AA) tS.toLeft r':=
    ⟨fun x i=> V.support x (.inl i),fun i x=>V.sto i (.inl x),fun i h=>V.account (.inl i) (Finset.mem_toLeft.mp h),fun x i h=> V.location x (.inl i) (Finset.mem_toLeft.mp h)⟩
def chairs₂ (V: (mural A Ba AA).Basis tS r') : Basis Ba tS.toRight r':=
    ⟨fun x i=> V.support x (.inr i),fun i x=>V.sto i (.inr x),fun i h=>V.account (.inr i) (Finset.mem_toRight.mp h),fun x i h=> V.location x (.inr i) (Finset.mem_toRight.mp h)⟩
lemma currents (V: (mural A Ba AA).Basis tS r')(u:α):
    (M₀).sector u tS V=(Lobby.peel A AA).sector u tS.toLeft (chairs₁ A Ba AA tS V)-Ba.sector u tS.toRight (chairs₂ A Ba AA tS V):=by
   funext x U; change _=(Lobby.peel A AA).sector u tS.toLeft _ x U-Ba.sector u tS.toRight _ x U; unfold Manor.sector; rw [sum_sum_eq_sum_toLeft_add_sum_toRight, sub_eq_add_neg,← Finset.sum_neg_distrib]
   congr 1; exact sum_congr rfl (fun i _=> by simp [Lobby.mural,Lobby.peel,Lobby.unison,Lobby.signed,chairs₂])

variable {A Ba AA tS}

abbrev Ring := Pier c G W x μ L Q o C β χ α
variable {Y:Slide.Stars→Side}
variable {Vv:∀ i:Stars, Pier (Y i) G W x μ L Q o C β χ α}(Yx:∀ i:Stars,Pier.Cuts Q χ (Vv i))
variable (R: ∀ i, Chairs Q (Vv i) (Yx i) r')
def surge₁ (u:α)(i:Stars):= (Pier.vane Q χ (Vv i)).sector u (Yx i).A (R i).raw
def surge₂ (u:α)(i:Stars):= (Vv i).spill.sector u (Yx i).B (R i).model
def surge (u:α):= (surge₁ Q Yx R u)-(surge₂ Q Yx R u)
local notation "OP" => surge Q Yx R
lemma leaned (u:α)(i : Stars) : Trio.froth (OP u i)=(Apo.slab (Pier.vane Q χ (Vv i)) (Yx i).A u - Apo.slab (Vv i).spill (Yx i).B u):=by
    rw [← froth_price _ (Yx i).A (R i).raw u, ← froth_price _ (Yx i).B (R i).model u]
    funext Z; exact Finset.sum_sub_distrib (f:=fun j=> surge₁ Q Yx R u i j Z) (g:=fun j=> surge₂ Q Yx R u i j Z)
local notation "PP"=> Pier.Receipts
lemma major (u:α)(i:Stars)(ht : Pier.Receipts Q (Vv i) P' (Yx i) R' p₀) : ∃ t:ℝ, Portal.Mare P' (Trio.froth (surge Q Yx R u i) -fun _=>t) β R' p₀ :=by
   rw [leaned Q Yx]; exact ⟨_,(ht.heard _).2⟩ -- edit

variable {σ₁ σ₂ σ₃ σ₄ σ₅:ℝ}
structure Costs (P':BudgetPoint)(u a v:ℝ) : Prop where
   first i : Manor.Templary (Pier.vane Q χ (Vv i)) ((Yx i).A:Set (staff Q χ (Vv i))) (Flues.candle (Vv i).pose (Vv i).starts (Vv i).stepP) P' a u -- Staff syntax
   second i : Manor.Templary (Vv i).spill ((Yx i).B:Set (Vv i).token) (Vv i).root P' a v

variable (h: Costs Q Yx P' σ₁ a σ₂)
include h
lemma regularV (u:α) (i:Stars)(x:Site (Y i)): P'.Regular univ (OP u i x):= AnalyticBridge.CouplingShape.reg_extend (AnalyticBridge.CouplingShape.reg_sub
   (((vane Q χ (Vv i)).networks u _ P' _ (h.first i) x (Nat.le_refl _)).1) (((Vv i).spill.networks u _ P' _ (h.second i) x (Nat.le_refl _)).1)) (subset_univ _)
lemma hazel (ha:0 ≤ a)(u:α) (i:Stars)(x:Site (Y i))(V:Config G (Y i))(hv: flags P'.threshold V=∅) : ‖OP u i x V‖ ≤ ballCost r'*σ₁+ballCost r'*σ₂:=by
   have hV : Healthy P'.threshold (neighbors r' x) V:=by simp [Healthy,hv]
   change ‖ (Pier.vane Q χ _).sector _ _ _ x V-(Vv i).spill.sector _ _ _ x V‖ ≤ _
   rw [← Manor.onSector _ _ _ P' _ _ _ hV, ← Manor.onSector _ _ _ P' _ _ _ hV]; exact (norm_sub_le ..).trans (add_le_add ((vane _ _ _).coupons u _ P' _ (h.first i) x V ha) ((Vv i).spill.coupons u _ P' _ (h.second i) x V ha))
end
end YM.RemainderComparison.Funk
