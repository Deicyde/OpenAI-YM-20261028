import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Posts
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Planning


/-!
# Pre-L vs after-L votes: arithmetic only

At each STAGE and family request d, prepare entries before L incl
Brevity and Steel. Transport to any smaller post-L rate, needed e.g.
for Eta threshold payments in Opacity/. Doesn't assert Heaters nor
choose a history. Don't pull unmasked budgets backward in time.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank
open Lattice Wilson Pressure RG Next.Rank Next.Rank.Perch Tapes Peak Flux Marker Ac Corona Value Precision RankCovariance Display Display.Docking Filter RG.Supply Next.Rank.Station Finset Bid
open scoped Topology BigOperators Classical
variable {G : Gauge}
lemma fragrant {e : ℝ} (h : 0<e) : ∃ k : ℕ,∀ L : Side, k ≤ L.val → Tab L e := by
  obtain ⟨k,hk⟩:=exists_nat_ge (10*(15:ℝ)^4*Docking.increment e/e)
  exact ⟨k,fun L hp=> ⟨h.le,(div_le_iff₀ h).1 (hk.trans (Nat.cast_le.mpr hp))⟩⟩

-- post stability
section
variable (p : Purse) (a : ℝ)
def trim (p : Purse) (a : ℝ) (h : 0<a) : Purse := { p with
    era:={ p.era with coast:={ p.era.coast with a:=a, posA:=h } }
    spend:=p.spend
    warp:=p.warp
    hour:=p.hour
    common:=p.common }
lemma trimmed (h : 0<a) (ht : a ≤ p.era.coast.a) {L : Side} {b : Stage}
    (hp : Regiment p b L) : Regiment (trim p a h) b L := by
  obtain ⟨h0,⟨h1,h2,h3,h4,h5⟩,⟨hh,hT,hR⟩,hg,hp,hy,hv⟩:= hp
  exact ⟨h0,⟨h1,h2,h3,h4,h5⟩,⟨hh,ht.trans hT,hR⟩,hg,hp,hy,hv⟩
lemma brief_trim (h : 0<a) {B : MapPrices} {C j L} (he : Brevity (G:=G) B C j p L): Brevity (G:=G) B C j (trim p a h) L:= ⟨he.capital,he.width,he.pulse,he.credits,he.ceiling⟩
def curtain {d : ℕ} (P : Tapes.Panel d) (y : ℕ → ℝ) (h : ∀ i,0<y i) : Tapes.Panel d := {P with
  bag j:= trim (P.bag j) (y j) (h j)
  factor:=P.factor
  stable:=P.stable
  loose:=P.loose
  vital:=P.vital }
end

variable (X : Sheet G) (B : MapPrices)
structure EntryHold {j : ℕ} (s : Tapes.Entry (X.profile j)) : Prop where
  earn : capital X.kernel B j ≤ s.kernel
  space : 30≤s.posts
  billing : 8 * salary (s.trunk+2) ≤ s.shape ∧ 8*salary s.trunk ≤ s.shape
lemma entries (j : ℕ) : ∃ Z : Tapes.Entry (X.profile j), EntryHold X B Z:= by
  let p:=X.profile j; let s:= p.supportExponent; let a:=max (8*salary s) (8*salary (s+2))
  let T : Tapes.Entry p:= ⟨max 1 (capital X.kernel B j),le_max_left ..,max 1 a,le_max_left ..,30,by decide,40,le_rfl,p.clip.linear/20,div_pos p.clip.tail_pos (by norm_num),le_rfl,s,le_rfl⟩
  exact ⟨T,le_max_right ..,le_rfl,(le_max_right ..).trans (le_max_right 1 _),(le_max_left ..).trans (le_max_right 1 _)⟩
structure PreStand (P : ∀ d,Tapes.Panel d) (k : ℕ→ Finset ℕ) (M : ℕ→ℕ) : Prop where
  reg : SizeBook X k P M
  potion i j (h : i ∈ k j) L (hp : M j ≤ L.val): Brevity (G:=G) B X.kernel j ((P i).bag j) L ∧ Steel ((P i).bag j) (X.profile j) L

lemma cultivate (S : ∀ (_ j : ℕ), Tapes.Entry (X.profile j)) (b : ℕ → ℝ) (h : ∀ d, d+6 ≤ b d) (hs : ∀ i j,EntryHold X B (S i j)) (hv : Tendsto (fun j=>(X.profile j).order) atTop atTop) :
    ∃ (P : ∀ d : ℕ, Tapes.Panel d) (k : ℕ → Finset ℕ) (M : ℕ → ℕ),
      (∀ i,(P i).arc=b i ∧ ∀ᶠ j in atTop,i∈k j) ∧ (∀ j i,i∈k j→Compatible (P i) j (S i j)) ∧
        (X.floorL ≤ M) ∧ PreStand X B P k M:= by
  obtain ⟨P,k,M,hI,hC,hL,hR⟩:= growth S b h hv
  have ht i j (h:i∈ k j) : ∃ y : ℕ,∀ (L : Side),y ≤ L.val → Brevity (G:=G) B X.kernel j ((P i).bag j) L ∧ Steel ((P i).bag j) (X.profile j) L:= by
    obtain ⟨-,h6,-,h5,he,h7,-⟩:= hC j i h
    obtain ⟨n,hn⟩:= sizing_gap (B.Ω j) G
    let Q:= S i j; have hr : 0 < Q.trunk := (X.profile j).price_pos.trans_le Q.road
    obtain ⟨u,hU⟩:= fragrant hr; obtain ⟨z,hZ⟩:= fragrant (show 0<Q.trunk+2 by linarith only [hr]); obtain ⟨h1,h2,h3⟩:= hs i j
    let s:= X.profile j; let E:=(P i).bag j; let d:=s.supportExponent; have ht:0 < d:= s.price_pos
    obtain ⟨r,hh⟩:= exists_nat_ge (10*(15:ℝ)^4 * Docking.increment (load E.era+1)/d)
    refine ⟨n+u+z+r+M j,fun v hV=>⟨⟨?_,?_,hn v (by omega),?_,?_⟩,(div_le_iff₀ ht).mp (hh.trans (Nat.cast_le.mpr (show r≤_ by omega))),((hR i j h).2 v (by omega)).1.aptitude.1⟩⟩
    · rw [h5]; exact h1
    · rw [h6]; exact h2
    · rw [load,h7,he]; exact h3
    rw [load,h7]; exact ⟨hZ v (by omega),hU v (by omega)⟩
  choose! t hT using ht
  exact ⟨P,k,(fun j=> max (M j) ((k j).sup fun i => t i j)),hI,hC,fun j=> (hL j).trans (le_max_left ..),
    ⟨fun i j hp=> ⟨(hR i j hp).1,fun L hL=> (hR i j hp).2 L ((max_le_iff.mp hL).1)⟩,fun i j hp L hL=> hT i j hp L ((le_sup hp).trans ((max_le_iff.mp hL).2))⟩⟩

-- Rate Ψ,K,Q etc can remain unchanged for weight tickets;
-- post positivity does NOT change lengths nor claims to have reached that rate.
lemma recultivate {P k M} (h : PreStand X B P k M) (z : ℕ →ℕ→ℝ) (hp : ∀ i j,0<z i j) (hv : ∀ i j, z i j ≤ ((P i).bag j).era.coast.a) :
    PreStand X B (fun i=> curtain (P i) (z i) (hp i)) k M := by
  refine ⟨fun i j hh=> ⟨(h.reg i j hh).1,fun L hz=>?_⟩,fun i j hh L hz=> ⟨brief_trim _ _ _ (h.potion i j hh L hz).1, (h.potion i j hh L hz).2.1,(h.potion i j hh L hz).2.2⟩ ⟩
  obtain ⟨hv',hp'⟩:= (h.reg i j hh).2 _ hz; exact ⟨trimmed ((P i).bag j) (z i j) (hp i j) (hv i j) hv',hp'⟩

end YM.PhysicalNext.InteractingRank
