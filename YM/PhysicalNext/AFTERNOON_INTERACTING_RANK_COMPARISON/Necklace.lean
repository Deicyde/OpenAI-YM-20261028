import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Estate
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Payout
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Voyage
import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Wakeful
/-!
# Burn head for the actual normalizer continuation

Request a scalar reweighting (at the whole
background) tied to the *new* exponent/E, symmetric small real
boundaries, on all fields.

And same unmarked `Opacity` (which
Opacity/ directory goes on to prove, NOT including this red).

NOT asking for a one-step normalized marker connection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Display.Sew
open Lattice Wilson Pressure RG MeasureTheory Function Next.SectorChange Matrix Finset
     Tree Push.SectorMeasure Next.Rank Tapes Value Marker Ac Glyph Thirst Docking
     Flux Bid SectorNext.Vacuum Precision Baler
open scoped Topology BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {x τ : ℝ} {L : Lantern G S} {T : Tube G S} {O : Orchard S}
    {P : Teller G} {W V ι κ α β : Type} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V] {u : W → Site c} {v : V→Site c} [Fintype ι] [Fintype α]

section
-- sanitize Empty.DE paths by real constructors
def blank (c : Side) : Empty → Site c := Empty.elim
lemma blink (S : StepData c f) : blank c=S.ratio.parent ∘ blank f:= funext (fun t=> t.elim)
structure Rim (τ : ℝ) (G : Gauge) (c : Side) where
  X : Support c
  area : X.Nonempty
  letter : Config G c → ℝ
  gauge : GaugeInvariant letter
  obeys U : Healthy τ X U → letter U=0
  reads : UsesFinal τ X letter
  money : Measurable letter

def Rim.cash (p : Rim τ G c) (θ : W→ Site c) : CoverReads G θ τ :=
  ⟨p.X, p.area,Glyph.quiet W,fun _ h=>False.elim (notMem_empty _ h), (fun a=> (p.letter a:ℂ)),Complex.continuous_ofReal.measurable.comp p.money,fun x y h H=>congr_arg Complex.ofReal (p.reads x y h H),fun t a=> congr_arg Complex.ofReal (p.gauge t a)⟩
def wingspan (p : α→Rim τ G c) (θ : W→Site c) := fun i=>(p i).cash θ
omit [Fintype α] in
lemma rim_b (p : α→Rim τ G c) (θ : W→Site c) : Boundary (wingspan p θ):= by
  constructor; exact fun _=>rfl
  intro i U h; change (↑((p i).letter U):ℂ)= _; rw [(p i).obeys U h]; simp only [Complex.ofReal_zero]
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η β s M l k m σ h y w : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    (v : Config G c→ℝ) {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
local notation "rb" => R'.p
local notation "X0"=> unmarked R R' p A hs (blink S) hR
local notation "G0"=> germ X0 A
local notation "F0"=> gruel X0 A (callsQuiet R R' p A hs hR (blink S))
local notation "Y0"=> wingspan E (blank c)
structure Opacity (e M N d : ℝ) : Prop where
  roofs : BodyGrant T R L D J R'.p.threshold p (fun a=> (v a:ℂ))
  cash : Holdings R' p T M N (e+1) d
  voyages s t : Nonempty (Voyage X0 s t)
  realistic i A k V z : Sound ((p i).weight A k V z)

/-- Actual scalar identity v * unforced background gas =
exp(R'.exponent) * product of flag-boundary correction factors.

**No**
hole dependence asked for here (produced in Discs).

Works in old memory
of Empty probe labels.

Includes quantitative and symmetry conditions on
those factors. -/
structure Resin (e y : ℝ) : Prop where
  each U : v U* realGas G0 rb ∅ U= Real.exp (R'.exponent U) * ∏ i, ((E i).letter U+1)
  guards : ∃ c : α→ℝ,(∀ i, 0≤c i) ∧ (∀ i V, ‖(E i).letter V‖≤ c i) ∧ Hits (fun i=>(E i).X) c R'.p (ucap e) y
  brings s i : ∃ H, Changing (pull s i) (StepData.sendSites s i) H (witness Y0) (witness Y0)
-- committed prior to all placements.
end
section creation
variable (R : Rep G f) (R' : Rep G c) (p : ι→ Zest G S x L.park R'.p.threshold) (A : Boosted T P x) (hs : 25*radiusB x+30 ≤ R'.p.B)
    {o ℓ δ Λ η β s M l k m σ h y w : ℝ} (hR : R.Lawful o ℓ Λ δ η)
    {ν : Config G c→ℝ} {D : Allocation G S x w} {J : ChartRatio G}
    (E : α→ Rim R'.p.threshold G c)
    (he : Opacity R R' p A hs hR ν (D:=D) (J:=J) k M l σ)
local notation "rb" => R'.p
local notation "X0"=> unmarked R R' p A hs (blink S) hR
local notation "G0"=> germ X0 A
local notation "F0"=> gruel X0 A (callsQuiet R R' p A hs hR (blink S))
local notation "H0"=> (fun i=> Sum.inl (scroll G0 i) : Glade c → Lining G (blank c) R'.p.threshold)
local notation "Y0"=> wingspan E (blank c)
abbrev courtyard := toRain (toRain F0 H0) (witness Y0)
local notation "V0" =>courtyard R R' p A hs hR E

def germinates := enrolling R' V0
local notation "Q"=> germinates R R' p A hs hR E
variable (θ : W→Site f) (u : W→Site c) (hθ : u=S.ratio.parent∘θ)
local notation "X"=> unmarked R R' p A hs hθ hR
local notation "H"=> germ X A
local notation "F"=> gruel X A (callsQuiet R R' p A hs hR hθ)
local notation "G1"=> wingspan E u
local notation "K"=> toRain (toRain F (fun i=> Sum.inl (scroll H i))) (witness G1)
include he
lemma genuine : ∀ i A k V y, Sound ((X i).lamp A k V y):=by
  rintro ((i|i)|i) A k V y; exact he.realistic ..; exact vouch _; exact i.elim
lemma worth_real (i : Club X) U : Sound (letter X (T:=T) i U):= Sound.money T (fun U' k V y=> Sound.prod _ fun i=> genuine R R' p A hs hR he θ u hθ i U' k V y)
omit he [Fintype α] in
lemma toeMap : ∃ Ω, Waking id (Equiv.refl (Site c)) Ω V0 K:=by
  let t:= arrested R R' p A hs hR (blink S) hθ hR
  have h' U: flags R'.p.threshold U=(flags R'.p.threshold ((@id (Config G c)) U)).map (Equiv.refl _).toEmbedding:= by ext i; simp
  let hZ:=(growth R R' p A hs hR (blink S) hθ hR).locked _ h'
  let L:=t.shuttered hZ h'
  have hw : Changing id (Equiv.refl _) (Equiv.refl _) (witness Y0) (witness G1):=by
    refine ⟨fun i=> ?_,fun _ _=>rfl,fun _=>rfl,fun _=>rfl⟩; change (E i).X=(E i).X.map _; ext; simp
  exact ⟨_,L.shuttered hw h'⟩
lemma registrants : Background Q K:= by
  have hz i U: Sound (Value.Lifted.value (F i) U):= by unfold gruel foundering; dsimp only; split; exact worth_real R R' p A hs hR he θ u hθ i.val U; exact vouch 0
  have h₀ i:(F i).fires=quiet W:= Across.rises (callsQuiet R R' p A hs hR hθ) i.val.val
  have hW' (i) (U): Sound ((K i).value U):=by
    refine chirping (blanking h₀ (fun _=> rfl)) (fun _=>rfl) (chirping h₀ (fun _=>rfl) hz (fun i U=>?_)) (fun i U=> vouch _) i U
    change Sound (((scroll H _).glow R'.p.threshold).value U); rw [scroll_value]; exact vouch _
  obtain ⟨F',hF⟩:=toeMap R R' p A hs hR E θ u hθ
  have hW i U: Sound ((V0 i).value U):= hF.values i U|>.symm ▸ hW' _ U
  have hx : Background Q V0:= chairMap _ _ hF.quiet hW
  intro i U; refine Eq.trans ?_ (hx i U)
  symm; unfold Value.column; apply Fintype.sum_equiv F'; intro j
  simp_rw [hF.quiet,hF.fresh,true_and]
  have hh:(V0 j).inventory=(K (F' j)).inventory:= by rw [hF.inventory]; ext; simp
  have hv:(V0 j).extent=(K (F' j)).extent:=by rw [hF.extent]; ext; simp
  apply if_congr; rw [hh,hv]; exact hF.values j U; rfl
-- Carves on THIS mark stencil, through subsequent W:H data

def carves : Flux.Vac u Q:=⟨_,_,_,F,scroll H,G1,(fun i=> Across.rises (fun _=>callsQuiet ..) i.val.val), (fun _=>rfl),rim_b E u,registrants R R' p A hs hR E he θ u hθ⟩
-- Uses voyage(s) to construct Moves
lemma travelers (fR : Resin R R' p A hs hR ν E k y) (h : ∀ s i, Nonempty (R'.activities.Moves s i)) : ∀ s i,Nonempty ((Q).activities.Moves s i):=by
  refine transported _ _ (fun s i=> ?_) h
  obtain ⟨U⟩ := he.voyages s i
  obtain ⟨D,hK⟩:= fR.brings s i
  have hV:= U.rebuilt A
  have hx U : flags R'.p.threshold (U : Config G c)=(flags R'.p.threshold (pull s i U)).map (StepData.sendSites s i).toEmbedding:= dispatched ..
  have hW : Holy (U.orientation.exe) (pull s i) (StepData.sendSites s i) G0 G0:=by refine ⟨fun j=> (U.orientation.zone_covers j.val), fun j W=> (Voyage.tribute U A j.val W).symm⟩
  exact ⟨_,(hV.shuttered (hW.locked R'.p hx) hx).shuttered hK hx⟩
end creation
end YM.PhysicalNext.InteractingRank.Display.Sew
