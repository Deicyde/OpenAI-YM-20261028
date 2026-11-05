import YM.MergeProof.Biscuit
import YM.MergeProof.North.Clause
import YM.MergeProof.South.Wakes

set_option autoImplicit false
noncomputable section
namespace YM.MergeProof
open Finset Function Filter MeasureTheory Lattice Wilson RG Push Marker Source Extra.Histories
open Planned.GuardedAtom Next.Rank Edition Spindle Extra.Multi Motion Local Bid Cells Extraction Exponential Overlay
open Accent MergeProof.Float PhysicalNext.Repeat Lotus
open scoped Topology Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G:Gauge}(C:Family G)(N k m p d:ℕ)(H:C.Makes)
variable {W:Worth}{u ψ φ δ:ℕ→ℝ}{r:ℕ→ℕ}{ζ:ℕ→ℕ→ℝ}{D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)}
variable (w:ℝ){j:ℕ}
set_option quotPrecheck false
open Relay
local notation "T"=> C.path
local notation "ℓ"=> C.ref d
local notation "F"=> C.labels.level d
local notation "Y!"=> C.localSection d
local notation "a!"=> C.S.a
local notation "s!"=> C.factory d N p
local notation "R"=> C.path.rep N p
local notation "ζ!"=> ζ d
variable (h:Scrim C W u ψ φ δ ζ r D) (L:Stock.Tabs C.path.levels)
variable {o:∀ i,Site (C.side i p)}(a:Motion) (Z:∀ i:ℕ,Coefficient (C.labels.level d) (C.side i p)) {g :ℕ→ℝ}
    (hK:C.ref d ≤ m)(hk:m≤k)(e:k≤N)(hw:0<w)(hS:∀ i ≥ m,i<k→ o (i+1)=(C.path.levels.clock.op i p).ratio.embed (o i))
abbrev stair (φ:ℕ→ℝ)(w:ℝ)(m:ℕ) := fun i=> march (fun _:Unit=>w) φ m i ()
local notation "τ"=> stair φ w m
local notation "f"=> liftF T Y! N p a o Z
local notation "Λ"=> liftK T N p a o Z
include h H hK hk e hw hS
lemma beams (he:Club T C.params Y! (ζ d) ψ m k N p (τ) D Z g e) :∃ G', Wakes T m k N p o τ f G' D e∧ (∀ i≥m,i≤k → profile (R i).activities (G' i)=Λ i ∧ Integrable (coin (R i) (f i) (G' i)) (prior G _)) ∧ ∀ U,w*‖(f m) U‖ ≤ 2 ∧ w*(∑ i:Box (C.side m p),‖profile (R m).activities (G' m) i U‖)≤1:=by
    have hF:Brine C.path m δ φ:=⟨fun i _=> h.costs.stay.water _ (Nat.zero_le i),fun i _=> h.costs.stay.mint _ (Nat.zero_le i),fun i _=> h.costs.stay.split _ (Nat.zero_le i),fun i _=> h.costs.stay.support _ (Nat.zero_le i)⟩
    obtain ⟨Y,hΛ,hγ,_⟩:= h.costs.heights d m N p hK (hk.trans e); let x:= τ; have hp' i (he:m ≤ i): 0 < x i:= march_pos _ _ _ _ _ (fun _=>hw) hF i he _
    obtain ⟨t,hT,hσ⟩:= chapter T C.params Y! (ζ d) ψ m k N p a o x D Z g H.wilson (H.sections d) e he (fun j hj _=> hp' _ hj) (fun j hj _=> by rw [show x (j+1)=φ j*x j from by unfold x stair; simp only [march,if_pos hj]]; exact mul_le_of_le_one_left (hp' _ hj|>.le) (hγ.level j hj)) hΛ hS (fun j _ hj=> by obtain ⟨w,p,hx,hv⟩:=h.costs.night.days N p j (hj.trans_le e); exact hx.propagate)
    refine ⟨t,hT,fun j hj ht=> ⟨hσ j hj ht,?_⟩,fun U=>?_⟩
    · have hz:= he.ticks j hj ht; obtain ⟨X,hQ,hh,hα⟩:= sparkling T C.params Y! (Z j) a (o j) (alto T j d) H.wilson 0 (ht.trans e) (H.sections d) hz.1 hz.2
      rw [coin_port _ _ (hT.stocked j hj ht) hh ((hσ j hj ht).trans hQ) ((H.wilson.represents _ _ _ (ht.trans e)).good.labels), liftF,hα]
      exact (tint _ _ _ (play_integrable T N H.wilson (ht.trans e) hz.1 hz.2)).smul _
    have hi:=he.rates m le_rfl hk; unfold stair at hi; rw [marines m φ _ (fun _=>hw)] at hi
    rw [hσ _ le_rfl hk]; exact toasted C N m p d H Z (ζ d) hK (hk.trans e) a (o m) (he.ticks _ le_rfl hk|>.2) hw.le hi (hΛ.coin m le_rfl) U
end YM.MergeProof
