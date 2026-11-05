import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Meter
import YM.AnalyticBridge.LOCAL_GAUSSIAN_MULTIPLIER.Lens
import YM.AnalyticBridge.SHARP_NORMALIZED_TAIL.Accumulator
import YM.Next.FREE_KERNELS.Lifts
import YM.SectorNext.RECONNECTED_LOCALITY.Radiance

set_option warningAsError false

/-!
# Account terms actually need only the numerical stencils

Compulsory H_D `work...` costs. Include mask range under aperture. No
analogous statements for long cutoff tails still retained outside. To
charge true supports then still need the possible-geometry query receipts
and support joining; F and A unchanged in these comparisons.
-/
set_option autoImplicit false
noncomputable section
-- Adapted directly from YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Meter near-receipt proof,
-- need SEPARATE C,L,D rows and not only their combined contribution.
namespace YM.PhysicalNext.Dictionary.Voice.Meters
open AnalyticBridge.Annulus.Map
open Function Filter Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree Finset
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.Fluctuations Next.SectorChange Bid
open YM.SectorNext.Remainder.Affine
open Work.E03 (sep_step parent_step sep_walk stop_route casted_endpoint)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n m : Side} {S : StepData c f}

section works
variable {α β ι θ : Type*}

-- Variant of the internal RowNear of Next.FLUCTUATIONS.Locality,
-- expose both directions for even zip(V-dependent) reader use here.
private structure Peers (P : Config G c → α → β → Pressure.Pay G) (p : α → Site c) (q : β → Site c) (d : ℕ) : Prop where
  remote U i j : d < separation (p i) (q j) → P U i j = 0
  peer U V i j : AgreeNear id (p i) d U V → P U i j = P V i j

private lemma peer_lane (P : Row ι θ) (p : α → Co c ι) (q : β → Co c θ) (r d : ℕ) (hd : 1≤d) :
    Peers (fun U i j => lane r d U P (p i) (q j)) (Prod.fst∘p) (Prod.fst∘q) r (G:=G) := by
  have hl {i : Cover} (h : (route 0 i 1).length*d ≤ r) := (le_mul_of_one_le_right (Nat.zero_le _) hd).trans h
  constructor
  · intro U i j h
    have hz (b : Cover) : priced r d U P (p i) (q j) b=0 := by
      unfold priced; split
      next hi =>
        have he : stop (p i).1 (route 0 b 1) = (p i).1 + wrap c b := by
          simpa only [map_zero, add_zero] using stop_route (p i).1 0 b
        have hh : separation (p i).1 (q j).1 ≤ r := by
          rw [hi.2]; refine le_trans ?_ (hl hi.1)
          have ht := sep_walk id (fun x i => sep_step (c:=c) x i) (p i).1 (route 0 b 1)
          rw [←he]; exact ht
        exact (h.not_ge hh).elim
      rfl
    simp only [lane,hz,tsum_zero]
  intro U V i j h
  refine tsum_congr fun u => ?_; unfold priced; split
  next hi => rw [rated,rated,travel_near id (fun x i => sep_step x i) _ _ _ _ r (hl hi.1) h]
  rfl

private lemma peer_leap (T : Tube G S) (d : ℕ) :
    Peers (T.Φ d) (fun i => S.ratio.parent i.1.1) (fun i => i.1.1) d := by
  constructor
  · intro U i j h
    have hz (u : Cover) : casted S T.R d U (mesh i) (mesh j) u = 0 := by
      dsimp only [casted]; split
      next hi =>
        let w := route (lift (S.ratio.residue (mesh i).1)) (S.patch.L.val • u) 1
        have hv := sep_walk S.ratio.parent (parent_step S) (mesh i).1 w
        rw [show stop _ w = _ from casted_endpoint S (mesh i).1 u, S.ratio.embed_parent, ←hi.2] at hv
        exact (h.not_ge (hv.trans hi.1)).elim
      rfl
    simp only [Tube.Φ,leap,hz,tsum_zero]
  intro U V i j h
  apply tsum_congr; intro u; dsimp only [casted]; split
  next ht =>
    have hv : AgreeNear S.ratio.parent (S.ratio.parent (mesh i).1) d (replica S.ratio U) (replica S.ratio V) := by
      intro e he; unfold replica; split
      · rfl
      exact h _ he
    rw [rated, rated, travel_near _ (parent_step S) _ _ _ _ d ht.1 hv]
  rfl

private lemma zip_seen [Fintype β] {P : Config G c → α → β → Pressure.Pay G} {p q} {r : ℕ}
    (h : Peers P p q r) {a b : β → G.Color} {U V : Config G c} {i : α}
    (hl : AgreeNear id (p i) r U V) (he : ∀ j, separation (p i) (q j) ≤ r → a j=b j) :
    zip (P U) a i = zip (P V) b i := by
  unfold zip; apply sum_congr rfl
  intro j _; by_cases hv : separation (p i) (q j) ≤ r
  · rw [h.peer _ V _ _ hl,he j hv]
  rw [h.remote U _ _ (lt_of_not_ge hv),h.remote V _ _ (lt_of_not_ge hv)]; simp

private lemma unzip_seen [Fintype α] {P : Config G c → α → β → Pressure.Pay G} {p q} {r : ℕ}
    (h : Peers P p q r) {a b : α → G.Color} {U V : Config G c} {j : β}
    (hl : AgreeNear id (q j) (r+r) U V) (he : ∀ i, separation (q j) (p i) ≤ r → a i=b i) :
    unzip (P U) a j = unzip (P V) b j := by
  unfold unzip; apply sum_congr rfl
  intro i _; by_cases hv : separation (q j) (p i) ≤ r
  · rw [h.peer _ V _ _ (hl.shrink (by omega)),he i hv]
  have ht := lt_of_not_ge hv; rw [separation_comm] at ht
  rw [h.remote U _ _ ht,h.remote V _ _ ht]; simp
end works

-- Loads from payment either orientation once comparing.
variable (T : Tube G S) (x : ℝ) (V V' : Config G c) (U U' : Config G f) (k k' : S.Choices)
variable (hx : Aperture S T x)

include hx
omit hx in
private lemma peerPay (T : Tube G S) (r) : Peers (T.Φ' r) Prod.fst (fun i => i.1.1) r :=
    peer_lane T.R.mn pole mesh _ _ S.patch.L.property
omit hx in
private lemma peerCo (T : Tube G S) (r) : Peers (T.N r) Prod.fst (fun i => i.1.1) r :=
    peer_lane T.R.o id mesh _ _ S.patch.L.property

lemma with_components (o : Site c) (hV : AgreeNear id o (4*radiusB x) V V')
    (hU : AgreeNear S.ratio.parent o (4*radiusB x) U U') (hk : TagNe S o (4*radiusB x) k k') :
    let R := till x; let t := fiery G x S.patch.L; let s := temp x; let Q := S.prediction U k; let Q' := S.prediction U' k'
    (∀ i : Cell f, S.ratio.parent i.1=o → T.workF R U V t s i=T.workF R U' V' t s i) ∧
      (∀ i : Bond c, i.1=o → T.workI R Q V s i = T.workI R Q' V' s i) ∧
      (∀ i : Cell c, i.1=o → T.workC R V s i = T.workC R V' s i ∧ T.workL R U Q V s i=T.workL R U' Q' V' s i ∧ T.workD R V s i=T.workD R V' s i) ∧
      (∀ i : Co c Gain, i.1=o → T.workN R V s i=T.workN R V' s i) := by
  intro R t s Q Q'
  let a (j : Twin f) := S.ratio.parent j.1.1; let b (j : Twin c) := j.1.1
  obtain ⟨d,hb⟩ := hx.coarse
  obtain ⟨e,ha⟩ := hx.fine
  have hl : R ≤ radiusB x := by unfold R till; omega
  have h0 := hx.scale
  have hh : separation o o = 0 := separation_self _
  have hv (i : Twin f) (h : separation o (a i) ≤ R) : AgreeNear S.ratio.parent (a i) (2*radiusB x) U U' := hU.shrink (by omega)
  have h₁ i (h : separation o (a i) ≤ R) := shortcuts x (parent_step S) i U U' hx.scale (Nat.le_refl 1) ha
    (anchored (hv i h) (by omega))
  have h₂ (i) (h : separation o (b i) ≤ R+R+R) := shortcuts x (fun i j => sep_step i j) i V V' hx.scale S.patch.L.property hb (hV.shrink (by unfold b at h; omega))
  have h₃ i (h : separation o (a i) ≤ R) : T.Mv R s V i=T.Mv R s V' i := received T x V V' hx _ (hV.shrink (by unfold a at h; omega))
  have h₄ (i : Bond c) (h : separation o i.1 ≤ R) : T.Mw R s V i=T.Mw R s V' i := side_received T x V V' hx i (hV.shrink (by omega))
  have h₅ (i : Bond c) (h : separation o i.1 ≤ R) : V i = V' i := hV i (by change separation o i.1≤_; omega)
  have hQ (i : Bond c) (h : separation o i.1 ≤ R) : Q i=Q' i := transmission T x U U' k k' hx i (hU.shrink (by omega))
    (TagNe.close _ _ k k' hk (by omega))
  have h₆ (i : Bond c) (h : separation o i.1 ≤ R) : Z S Q V i=Z S Q' V' i := by unfold Z; rw [h₅ i h,hQ i h]
  have h₇ (i : Co c Gain) (h : separation o i.1 ≤ R) : zip (T.N R V) (T.vision R s V) i=
      zip (T.N R V') (T.vision R s V') i := by
    apply zip_seen (peerCo T R) (hV.shrink (by omega)); intro j hj
    exact (h₂ j ((separation_triangle o i.1 (b j)).trans (by unfold b; omega))).2.1
  refine ⟨fun i hi => ?_,fun i hi => ?_,fun i hi => ?_,fun i hi => ?_⟩
  · have hv (j : Bool) : separation o (a (i,j)) ≤ R := by unfold a; rw [hi,hh]; omega
    unfold workF
    rw [(h₁ (i,false) (hv false)).2.2]
    apply congr_arg (fun z : ℝ => Pressure.crown T.up T.high R 1 t U' i + z); exact sum_congr rfl fun j _ => by
      rw [h₃ (i,j) (hv j),Xf,Xf,(h₁ _ (hv j)).1]
  · have hs : separation o i.1 ≤ R := by rw [hi,hh]; omega
    unfold workI monetary wire; rw [h₅ i hs,h₆ i hs,h₄ i hs,hQ i hs]
  · have hp (j : Bool) : separation o (b (i,j))=0 := by change separation o i.1=0; rw [hi]; exact hh
    have h j := h₂ (i,j) (by rw [hp j]; omega)
    have hl j : T.vision R s V (i,j) = T.vision R s V' (i,j) := (h j).2.1
    have hx j : T.Xn R V (i,j) = T.Xn R V' (i,j) := (h j).1
    have he {α : Type} [Fintype α] {p : α → Site c} {P : Config G c → α → Twin c → Pressure.Pay G} (h : Peers P p b R) (j : Bool) (X Y : α → G.Color)
        (hh : ∀ i, separation o (p i) ≤ R → X i=Y i) : unzip (P V) X (i,j)=unzip (P V') Y (i,j) := by
      apply unzip_seen h (hV.shrink (by rw [hp]; omega)); exact fun a ha => hh a (by rw [← hi]; exact ha)
    have ha j := he (peer_leap T R) j _ _ (fun i h => (h₁ i h).1)
    have hb j := he (peerPay T R) j _ _ h₆
    have hd j := he (peer_leap T R) j _ _ h₃
    have hf j := he (peerPay T R) j _ _ h₄
    have hn j := he (peerCo T R) j _ _ h₇
    have hρ : crown T.down T.low R S.patch.L.val s V i = crown T.down T.low R S.patch.L.val s V' i := (h false).2.2
    change ∀ j : Bool, unzip (T.Φ R V) (T.Xf R U) (i,j) = unzip (T.Φ R V') (T.Xf R U') (i,j) at ha
    unfold workC workD workL
    simp only [hl,hx,hρ,hd,hf,hn,hb,ha]; trivial
  unfold workN; rw [h₇ i (by rw [hi,hh]; omega)]
end YM.PhysicalNext.Dictionary.Voice.Meters
