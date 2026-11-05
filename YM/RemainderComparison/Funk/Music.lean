import YM.RemainderComparison.Funk.Founder
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
open Lobby Portal
open Pier Slide
variable {β:ℝ}{χ:Chi}{ιa ιb δa δb:Type}(P': BudgetPoint)
open WickReps Manor Flues Serif
-- Work proof data-choices returned. Don't require any layout after masks as hypothesis. Represent crop BEFORE additional reset.
variable (H:Cash W x μ L Q o C T R)(Λ:Platform)(Ha:Currency)(M:ι→Portrait R α)(y:α)(l:ι→ℝ)(Z:Set ι)(E:Set ℕ)(v:ℝ)
local notation "A₀"=> Creek.theater H χ M y l Z v
local notation "Xv"=> brand M y
local notation "K₀"=> Creek.Academy H χ M y l Z v Λ.k
local notation "Rt"=> Flues.candle M y S
local notation "Lt"=> sits Z l v
local notation "a₀"=>Λ.a
-- Local economy.Yields. Interfaces separate Shape.Ce.Pl
variable (F:Manor G c ι α ιb) (E₁:Set ιb) (ℓ:ιb→ℕ) (V:Set (Sleet.Staff (Typeface.brand M y) H))
variable {C₁ D D₁ q t θ ξ bA Y U V₁ V₂:ℝ}{r' k m p z n I:ℕ}{Ω: KernelChoices}
local notation "Mʼ"=> Lobby.mural A₀ F K₀
local notation "N" => Verse.load
variable [Countable ι]
variable {P':BudgetPoint}
local notation "δQ"=> (gStep R.beta)^(Λ.p+1)
local notation "bK"=> ((unitK x)^4 * (gStep R.beta)^Λ.s)
local notation "uC"=> Ha.Y^Λ.k* Ha.spin
local notation "vC"=> Ha.Y^Λ.k* Ha.Y*Ha.spin*v
local notation "aC"=> Ha.e*U
variable {R':Rep G f}(H':Cash W x μ L Q o C T R')(D':Match.Alliance H' H 1 0)(f₁:ℕ→RegularAddress c) (f₂:ℕ→ Config G c→ℝ)
local notation "Tʼ"=> Flues.kettle H χ M y l Z v H' D' f₁ f₂
omit [Countable ι] in
lemma loosens (D:Yard ι α G c)(S:Set ι)(r:ℕ)(B:ℕ)(h:D.Pays S r B σ q) (hp:a ≤ σ)(hy:q≤t) : D.Pays S r B a t:=by
    obtain ⟨f,hf,hH,hV⟩:=h.wages; refine ⟨f,hf,fun i=> budget_loosen (budget_mono (hH i) ?_ ?_) hy,hV⟩
    · intro i; split; exact mul_nonneg (hf _) (Real.exp_nonneg _); exact le_rfl
    intro j; split; next=> exact mul_le_mul_of_nonneg_left (Real.exp_monotone (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))) (hf _)
    next=>rfl

-- PrÉludes together. Before kinetic comparison.
variable [Countable δ]
open Cargo
variable {Y':Stars→Side} {fA:Side} (Xa:∀ i:Stars,(Y' i).val=2*(n+i.val))(hf:2*n≤ fA.val)
variable (C':∀ i:Stars, Pier (Y' i) G W x μ L Q o C R.beta χ α)(S':δ→ Pier fA G W x μ L Q o C R.beta χ α)
variable (o':ι→Site c)(Wc:Breeze.Careers ι δ c o' r' Λ.k)(wp:ι→ℝ)
variable {u u₀ γ ψ B' b p₁ p₂ σ₁ σ₂ σ₃:ℝ}
-- one-level Civic: geometric post P support pay at σ with hZ≥P.supportExponent. header separately.

-- Phase.State Purchase pilots price aggregates & parent coverage
structure Goods : Prop where
   sovereign : Treasury (G:=G) (L:=L) Ω Λ Ha P' R.beta x
   distance : 0 ≤ σ ∧ 0 < r' ∧ σ+1≤Λ.a
   shade : 0 ≤ Funk.wages' Λ Ha P' R.beta x
   poses i : Pier.Enrollment Q Ω Λ Ha χ (C' i) P' ∧ Shadow Q (C' i) P' σ B'
   poses' i : Pier.Enrollment Q Ω Λ Ha χ (S' i) P'
   accounts : Caretaking H Λ Ha M y l Z E v (χ:=χ) (σ:=σ) P' p₁ B'
   rigging : Rigging P' G c r' z k n m R.beta Λ.R

structure Roster (P':BudgetPoint) (U b B' σ :ℝ): Prop where
   light : Originates H Λ Ha M y l Z E V χ v U
   beauty i : Pier.Materia Q Λ χ (C' i) P'∧ Beauty Q (C' i) P' σ B'
   culture i : Pier.Materia Q Λ χ (S' i) P'
   publishes : Shining (S:=S) (x:=x) Λ M y F E₁ ℓ P' σ B'
   orchestra : Cargo.Orchestra Q (Creek.theater H χ M y l Z v) F (Creek.Academy H χ M y l Z v Λ.k) V E₁ Z (Flues.candle M y S) C' S' o' Wc wp P'
   pension : (∀ i, 0≤ wp i) ∧ ∀ x:Site c, SumBudget (fun i=> if o' i=x then wp i else 0) b

local notation "φ"=> Funk.wages' Λ Ha P' R.beta x
local notation "d₀"=> paymentA z m σ φ P'
local notation "b₀"=>WickReps.burse P' k z φ* Manor.tribute m k (σ+1) (Breeze.areaBudget r' Λ.k b)
local notation "uPO"=> paymentB r' k m Y' (B'+p₂) B' p₂ (σ+1)
local notation "u₁"=> b₀+Manor.tribute m k (σ+1) ((ballCost r')*(uC+ vC + Λ.B))
local notation "KY"=> unitK x^4*gStep R.beta^I
variable (hg: Goods (r':=r') (z:=z) (n:=n) (k:=k) (m:=m) (σ:=σ) (P':=P') (Ω:=Ω) (B':=B') (p₁:=p₁) H Λ Ha M y l Z E v C' S') (hD:Roster H Λ Ha M y l Z E v F E₁ ℓ V C' S' o' Wc wp P' U b p₂ σ)
variable (hq:Flues.Resonant P'.B Λ.k (paymentB r' k m Y' (B'+p₂) B' p₂ (σ+1)) (unitK x^4*gStep R.beta^Λ.s) (WickReps.burse P' k z (Funk.wages' Λ Ha P' R.beta x)*Manor.tribute m k (σ+1) (Breeze.areaBudget r' Λ.k b)+Manor.tribute m k (σ+1) ((ballCost r')*((Ha.Y^Λ.k*Ha.spin+Ha.Y^Λ.k*Ha.Y*Ha.spin*v)+Λ.B))) σ (unitK x^4*gStep R.beta^I) σ₁ σ₂ σ₃)
local notation "Λʼ" => (Creek.spare H χ M y l Z v)
local notation "Talon"=>Cargo Q A₀ F K₀ Rt C' S' r'
include hg hD hq
-- Explicit consumption of coefficients on same layout. Transfer: no assumptions on E motion beyond REAL. Terminal First proof read estimates unnormalized.
set_option maxHeartbeats 1000000 in
lemma wisps : ∃ T: Talon, let t:=(Cargo.wall Q A₀ F K₀ Rt C' S' T)ᶜ
          Tolled H M y l Z v H' D' f₁ f₂ (χ:=χ) P' Λ.k ∧ (∃ I,Striped Q A₀ F K₀ V E₁ Rt C' S' T I) ∧ Underscore Q A₀ F K₀ Z Rt C' S' o' Wc T wp P' ∧ Thesaurus Q A₀ F K₀ Z Tʼ Xa hf Rt C' S' o' Wc T wp P' z k Λ.k σ d₀ b₀ KY uPO u₁ ∧
           Manor.Spinal Mʼ t Rt P' σ (7*δQ+aC+vC)∧ Manor.Templary Mʼ (t∩ Lobby.night Mʼ Z) Rt P' σ (7*δQ+p₁+vC):=by
    have ht:= hg.sovereign; have hp:= hD.publishes
    have hK:= hg.accounts; obtain ⟨U',hh⟩:= hK.launch
    obtain ⟨Q',F0,Y',n,hM,hL,hE,wp',hp'⟩:= hD.light.pale
    have ht' := Creek.mass₀ H χ U' M y l Z v hh hM P' ht.pose ht.pose2 ht.pose3 ht.pose4
    have hx':= Creek.mass₁ H χ U' M y l Z v hh hM P' ht.pose ht.pose2 ht.pose3 ht.pose4
    have hA: K₀ ⊆ {i| Muse.Pure Xv H χ Z Λ.k i}∪{i| impure Xv H χ Z Λ.k i}:=fun i hi=> Creek.monastery H χ M y l Z v hi
    have hj:= hp.rent; have hV:= Breeze.refers P' ht.root hp.bill; have hz:=hg.distance; have he:σ≤Λ.a :=(le_add_of_nonneg_right zero_le_one).trans hz.2.2; have h₁: Spinal A₀ K₀ Rt P' σ (uC+ vC):= ((ht'.swell hx').skim hA le_rfl he)
    have hm: Manor.Spinal Mʼ Set.univ Rt P' σ (uC+ vC+Λ.B) := by
       apply ((Lobby.sumPays (peel A₀ K₀) (signed F) P' Set.univ Set.univ ((Lobby.spinalize F P' Set.univ hV).skim (Set.Subset.refl _) le_rfl he) (Lobby.peeled A₀ P' K₀ h₁ (fun i _=> i.prop))).skim _ le_rfl le_rfl)
       intro i hi; cases i<;> simp [Lobby.switch]
    obtain ⟨w₃,hW,hV'⟩:= hD.light.regular
    have hHH:=(Creek.sheenT H χ U' M y l Z v hh hM P' ht.pose ht.pose2 ht.pose3 ht.pose4 E F0 Y' hL hE wp' hp' hK.earns he w₃ hW -- edit
       hV')
    let Uv:= {j: ↥K₀| j.val∈ Λʼ}
    have hy : Spinal Mʼ {i| (Mʼ).marks i=0} Rt P' σ (B'+ p₂):=by
       refine (Lobby.sumPays (peel A₀ K₀) (signed F) P' Uv (calm F) (Lobby.spinalize F P' (calm F) hD.publishes.rent) (Lobby.peeled A₀ P' K₀ hK.luxury fun i h=>h)).skim ?_ le_rfl le_rfl
       intro i h;cases i<;> exact h
    have hk:=Flues.gilded H χ U' M y l Z v hh hM H' D' f₁ f₂ P' ht.pose
    have hG:0< gStep R.beta:= (gS _ H.laws.intake.positive).1
    have hF': Manor.Spinal F E₁ᶜ Rt P' σ δQ:=(Breeze.sung (A:=E₁ᶜ) P' ht.root hp.bill (Set.subset_univ _) (fun i hi=> hp.short i hi)).skim (Set.Subset.refl _) ht.port he
    have hn:Manor.Templary A₀ ((K₀∩night A₀ Z)\V) Rt P' σ (4*gStep R.beta^Λ.s+p₁+vC):= hHH.2
    haveI :Nonempty α:=⟨y⟩
    obtain ⟨T,hpV,hU,hV,hx,hA⟩:= Cargo.sent Q Ω A₀ F K₀ V E₁ Z Tʼ Xa hf Rt C' S' o' Wc wp Λ Ha P' hg.sovereign hD.pension.1 hD.pension.2 (fun i=>⟨(hD.beauty i).1,(hg.poses i).1⟩) (fun i=>⟨hD.culture i,hg.poses' i⟩) (fun i=>⟨(hD.beauty i).2,(hg.poses i).2⟩) (pow_pos hG _) hD.orchestra hg.rigging hg.shade hz.1 hz.1 hz.2.1 hq (loosens _ _ _ _ hk hz.2.2 le_rfl) (Flues.aligned H χ U' M y l Z v H' D' P' f₁ f₂ ht.pose2) h₁ (hV.skim (Set.Subset.refl _) le_rfl he) hy hm.templary hHH.1 hn hF'
    have hs: (gStep R.beta)^Λ.s ≤ δQ:= pow_le_pow_of_le_one hG.le ht.coup ht.high
    refine ⟨T,tolling H Λ Ha M y l Z v H' D' f₁ f₂ ht U' hh hM χ rfl,hpV,hU,hV,hx.skim (Set.Subset.refl _) (by linarith only [hs]) le_rfl,hA.skim (Set.Subset.refl _) (by linarith only [hs]) le_rfl⟩
end YM.RemainderComparison.Funk
