import YM.RG08.Sideshow.Orbit
import YM.RG08.Mason.Hike
/-! # Repeated coefficient-stamp stability of full Kul graph.
- conditional phase-side & schedule announcements specified separately. Organize Run steps in
Ducat exchange. Polynomial horizon charges & top-age format. Allows geometry F,K=P as above
Cutoff dependence with initial boundary etc. Scheme on each compatible band.
-/
noncomputable section
set_option autoImplicit false
namespace YM.RG08.April
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason
open Function Jetty Lattice Precision Skiff Weald Hatch Planned.PrimaryIntegral295 Labels Source Source.Drops WardBin Parts Atrium Trill Necks Sideshow
open scoped Classical Matrix BigOperators PowerSeries Topology
variable {X Z:Type}{G:Gauge}{S:Rate.Stair X}{D d p l e n k r:ℕ}
local notation "Δ"=> stance (Loc G 1)
local notation "E"=> Ed G Cover

variable (F:Labels.Frame G d)
local notation "I₀"=>Accent F
local notation "P₀"=>Pack n E
local notation "B₀"=>Bouquet F

-- pair currencies at kiosk/turnstile. no γ clock assumption except Admits.
variable {W:Exchange Z}
def Blue (W:Ducat.Exchange Z)(D:ℕ)(σ:Z→ℝ)(hs:∀ i,0<σ i)(T U:Z→Pack n E):Prop:= ∃ (p q:Z→ℝ), W.Good p∧ W.cheap q∧ ∀ i, Sings Δ D (hs i) (T i) (p i)∧Sings Δ D (hs i) (U i) (p i)∧Sings Δ D (hs i) (T i-U i) (q i)
lemma blue_zero {σ:Z→ℝ}{hs:∀ i,0<σ i}:Blue (G:=G) (n:=n) W D σ hs 0 0:=⟨_,_,W.steady 0 le_rfl,W.zero,fun i=>⟨tin,tin,by simp only [sub_self];exact tin⟩⟩
lemma Blue.haul {O:Type}{Q:Exchange O}{U V:Z→Pack n E}{σ:Z→ℝ}{hs:∀ i,0<σ i}(h:Blue W D σ hs U V){f:O→Z}(he:Mason.String W Q f):Blue Q D (σ ∘ f) (fun i=>hs (f i)) (U ∘ f) (V ∘ f):=by
 obtain ⟨a,b,H,h,hb⟩:=h; exact ⟨_,_,he.golf a H,he.glow b h,fun i=>hb _⟩
-- matrix scalar tested meter here
variable {C:Type}
def Oil (W:Exchange Z)(A A':Z→ℝ):Prop:=∃ (p q:Z→ℝ),W.Good p ∧ W.cheap q ∧ ∀ z,|A z|≤p z ∧|A' z|≤p z∧ |A z-A' z|≤q z
lemma Oil.haul {O:Type}{Q:Exchange O}{A B:Z→ℝ}(h:Oil W A B){f:O→Z}(he:Mason.String W Q f):Oil Q (A ∘ f) (B ∘ f):=by obtain ⟨a,b,H,h,hb⟩:=h; exact ⟨_,_,he.golf a H,he.glow b h,fun i=>hb _⟩
lemma oil_zero :Oil W (fun _=>0) (fun _=>0):=by refine ⟨_,_,W.steady 0 le_rfl,W.zero,?_⟩; simp

-- all packs of a finite demand or family of tests gather via these.
lemma farmBlue {I:Type}[Fintype I]{n:I→ℕ}{U V:∀ i:I,Z→Pack (n i) E}{σ:Z→ℝ}{hs:∀ x,0<σ x}
   (H:∀ i,Blue W D σ hs (U i) (V i)):∃ (p q:Z→ℝ),W.Good p∧ (∀ x,1≤p x)∧W.cheap q∧∀ i z,
    Sings Δ D (hs z) (U i z) (p z)∧Sings Δ D (hs z) (V i z) (p z)∧Sings Δ D (hs z) (U i z-V i z) (q z):=by
 choose a b ha hb h using H
 let p:Z→ℝ:=fun z=>1+∑ i,a i z;let q:Z→ℝ:=fun z=>∑ i,b i z
 have hp:W.Good p:=W.hear _ _ (W.steady 1 zero_le_one) (crowd W _ _ fun i _=>ha i)
 have hq:W.cheap q:=shells W _ _ fun i _=>hb _
 refine ⟨p,q,hp,fun _=>le_add_of_nonneg_right (sum_nonneg fun i _=>W.safe _ (ha _) _),hq,fun i z=>?_⟩
 have he:a i z≤p z:=(single_le_sum (s:=univ) (f:=fun i=>a i z) (by intro i _; exact W.safe _ (ha i) z) (mem_univ i)).trans (le_add_of_nonneg_left zero_le_one)
 obtain ⟨h₁,h₂,h₃⟩:=h i z
 exact ⟨h₁.mono le_rfl le_rfl (fun _=>le_rfl) he,h₂.mono le_rfl le_rfl (fun _=>le_rfl) he,h₃.mono le_rfl le_rfl (fun _=>le_rfl) (single_le_sum (s:=univ) (f:=fun i=>b i z) (fun i _=>tiny W (hb i) z) (mem_univ i))⟩
lemma farmOil {I:Type}[Fintype I]{U V:I→Z→ℝ}(he:∀ i,Oil W (U i) (V i)):∃ (p q:Z→ℝ),W.Good p∧W.cheap q∧ ∀ i z,|U i z|≤p z ∧|V i z|≤p z ∧ |U i z-V i z| ≤ q z:=by
 choose a b ha hb h using he
 refine ⟨_,_,crowd W univ a (fun i _=>ha i),shells W univ b (fun i _=>hb i),fun i z=>?_⟩
 have hp:=single_le_sum (s:=univ) (f:=fun i=>a i z) (fun i _=>W.safe _ (ha i) z) (mem_univ i); have hq:=single_le_sum (s:=univ) (f:=fun i=>b i z) (fun i _=>tiny W (hb i) z) (mem_univ i)
 obtain ⟨h₁,h₂,h₃⟩:=h i z; exact ⟨h₁.trans hp,h₂.trans hp,h₃.trans hq⟩
end YM.RG08.April
