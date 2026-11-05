import YM.AnalyticBridge.ANNULUS_GAUSSIAN_INTERFACE.Map
import YM.Next.FREE_KERNELS.Dispatch
import YM.Next.ROTATIONS.Response
import YM.Next.SCHEDULE.Postal

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
namespace YM.AnalyticBridge.Annulus.Map
open Function Filter Lattice RG RG.Patch Precision Wilson Pressure Pressure.Stores Pressure.Tube Pressure.Teller Tree Finset
    YM.Push.SectorMeasure Oriented Exterior Bloch Next.Fluctuations Next.SectorChange Bid
open YM.SectorNext.Remainder.Affine
open Work.E03 (sep_step parent_step sep_walk stop_route casted_endpoint)
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical YM.Push.SectorMeasure ContDiff

variable {G : Gauge} {c f n m : Side} {S : StepData c f}

lemma anchored {E : Site n → Site c} {o : Site c} {r d : ℕ} {U V : Config G n} (h : AgreeNear E o r U V) (hh : d≤r) :
    AgreeNear E o d U V := fun i hi => h i (hi.trans hh)

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


end works

-- Loads from payment either orientation once comparing.
variable (T : Tube G S) (x : ℝ) (V V' : Config G c) (U U' : Config G f) (k k' : S.Choices)
variable (hx : Aperture S T x)

section fine
variable {q : Site n → Site m} (hq : ∀ x (i : Axis), separation (q x) (q (x+step i)) ≤ 1)
include hq

lemma face_near (i : Cell n) (U V : Config G n) (h : AgreeNear q (q i.1) 4 U V) : faceValue U i=faceValue V i :=
    travel_near _ hq U V _ _ 4 le_rfl h

lemma shortcuts {P : PathData G} {r : ℕ} {t C : ℝ} {p : Clip} (i : Twin n) (U V : Config G n)
    (hB : 120 ≤ radiusB x) (hr : 1≤r) (hl : LaneCounts P x t p C r q) :
    let R := till x
    AgreeNear q (q i.1.1) (radiusB x) U V →
    plotted P p R r U i = plotted P p R r V i ∧
      thinned P p t r R U i = thinned P p t r R V i ∧
      crown P p R r t U i.1 = crown P p R r t V i.1 := by
  intro R hv
  have he : R+4 ≤ radiusB x := by unfold R till; omega
  have h j := plotted_near q hq U V p P R r (i.1,j) hr (anchored hv he)
  have hh := face_near hq _ _ _ (anchored hv (show 4≤radiusB x by omega))
  have hf : shorten P R r U i.1 = shorten P R r V i.1 := by simpa [plotted] using h true
  have hp : PathData.kept p t i.1.1 U ↔ PathData.kept p t i.1.1 V := by
    have hh (W Y : Config G n) (h : AgreeNear q (q i.1.1) (radiusB x) W Y) : PathData.kept p t i.1.1 W → PathData.kept p t i.1.1 Y := by
      intro hw u; by_contra! hy
      have ht := hl.dropped Y i.1.1 u hy
      rw [← face_near hq u W Y (h.shrink (by omega))] at hy
      exact hy.not_ge (hw u)
    exact ⟨hh U V hv,hh V U (fun i hi => (hv i hi).symm)⟩
  refine ⟨h i.2,?_,?_⟩
  · unfold thinned toll shoot; simp [hp,hf,hh]
  unfold crown trunk; simp [hp,hf,hh]
end fine

include hx
lemma received (j : Twin f) (hV : AgreeNear id (S.ratio.parent j.1.1) (2*radiusB x) V V') :
    T.Mv (till x) (temp x) V j = T.Mv (till x) (temp x) V' j := by
  let R := till x
  have he : R ≤ radiusB x := by unfold R till; omega
  apply zip_seen (peer_leap T R) (anchored hV (by omega)); intro i hi
  obtain ⟨e,h⟩ := hx.coarse
  exact (shortcuts x (fun i j => sep_step i j) i _ _ hx.scale S.patch.L.property h (hV.shrink (by omega))).2.1

omit hx in
private lemma peerPay (T : Tube G S) (r) : Peers (T.Φ' r) Prod.fst (fun i => i.1.1) r :=
    peer_lane T.R.mn pole mesh _ _ S.patch.L.property
omit hx in
private lemma peerCo (T : Tube G S) (r) : Peers (T.N r) Prod.fst (fun i => i.1.1) r :=
    peer_lane T.R.o id mesh _ _ S.patch.L.property

lemma side_received (j : Bond c) (hV : AgreeNear id j.1 (2*radiusB x) V V') :
    T.Mw (till x) (temp x) V j = T.Mw (till x) (temp x) V' j := by
  have he : till x ≤ radiusB x := by unfold till; omega
  apply zip_seen (peerPay T (till x)) (anchored hV (by omega)); intro i hi
  obtain ⟨e,h⟩ := hx.coarse
  exact (shortcuts x (fun i j => sep_step i j) i _ _ hx.scale S.patch.L.property h (hV.shrink (by omega))).2.1

lemma transmission (j : Bond c) (hU : AgreeNear S.ratio.parent j.1 (radiusB x) U U')
    (hk : TagNe S j.1 (radiusB x) k k') : S.prediction U k j = S.prediction U' k' j := by
  have hz := hx.spans; unfold span at hz
  refine (prediction_near_eq hx.branched U U' k _ (anchored hU (by omega))).trans ?_
  exact same_tags k j k' U' (TagNe.close _ _ k k' hk (by rw [separation_self]; have ht := hx.scale; omega))


end YM.AnalyticBridge.Annulus.Map
